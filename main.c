/*!
 * \file smtpc/main.c
 *
 * \brief test smtp client
 *
 * \author Tony Finch <fanf2@cam.ac.uk> <dot@dotat.at>
 *
 * With thanks to:
 *
 * Chris Lightfoot <chris@ex-parrot.com>
 *	CRAM-MD5
 * Phil Pennock <pdp@spodhuis.org>
 *	64-bit cleanliness
 *
 * This is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2, or (at your option) any later
 * version.
 *
 * It is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * for more details.
 */

static const char camid[] =
"$Cambridge: hermes/src/smtpc/main.c,v 1.53 2010/02/08 16:50:58 fanf2 Exp $";

#include <sys/types.h>
#include <sys/socket.h>
#include <sys/stat.h>

#include <netinet/in.h>
#include <arpa/nameser.h>

#include <assert.h>
#include <err.h>
#include <netdb.h>
#include <pwd.h>
#include <resolv.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include <openssl/err.h>
#include <openssl/hmac.h>
#include <openssl/lhash.h>
#include <openssl/md5.h>
#include <openssl/rand.h>
#include <openssl/ssl.h>

/*!
 * \brief Expandable buffers.
 */
struct buf {
	char   *base;   /*!< Pointer to buffer. */
	size_t  size;   /*!< Size of the buffer. */
	char   *start;  /*!< Start of data in the buffer. */
	char   *end;    /*!< End of data in the buffer. */
	size_t  used;   /*!< Space between start and end. */
	size_t  space;  /*!< Space remaining after end. */
};

/*!
 * \brief Default buffer space/increment
 */
#define BUF_SPACE 1024

/*!
 * \brief Type of SASL authentication mechanism functions.
 *
 * The function is initially called with a state and challenge of
 * NULL, in which case it may provide an initial response to go with
 * the AUTH command. The return value of the function is passed back
 * as its state for the next step of the protocol. If the challenge is
 * not NULL then the function must return a response.
 *
 * \param state			The function's protocol state.
 * \param challenge		Decoded challenge from server,
 *						or NULL when requesting an initial response.
 * \param len_challenge Length of the challenge
 *						(which is not nul-terminated).
 * \param response      Mechanism function returns a pointer to
 *                      a malloc()ed response string via this parameter.
 * \param len_response  Length of the returned response string.
 */
typedef void *auth_fn(void *state,
    const unsigned char *challenge, size_t len_challenge,
    unsigned char **response, size_t *len_response);

static auth_fn auth_external, auth_login, auth_plain, auth_cram_md5;

struct auth {
	const char     *method;
	auth_fn        *function;
} auth_table[] = {
	{ "CRAM-MD5", auth_cram_md5 },
	{ "EXTERNAL", auth_external },
	{ "LOGIN", auth_login },
	{ "PLAIN", auth_plain },
	{ NULL, NULL }
};

static const char  *progname;           /*!< Program name for messages etc. */
static char         hostname[NS_MAXDNAME]; /*!< This machine's hostname. */

static int          auth_delay;         /*!< Delay auth parameters. */
static const char  *auth_method;        /*!< Authentication method. */
static const char  *auth_username;      /*!< Authentication username. */
static const char  *auth_password;      /*!< Authentication password. */
static size_t       auth_username_len;  /*!< username string length. */
static size_t       auth_password_len;  /*!< password string length. */

static int          debug_level;        /*!< Global debugging level. */
static int          mx;                 /*!< Use MX records. */
static int          pipeline;           /*!< Use SMTP pipelining. */
static int          timeout;            /*!< Connect timeout. */
static int          use_tls;            /*!< Use TLS. */
static int          verify;             /*!< Verify address(es). */
static int          tls_no_verify;      /*!< No server cert verification. */
static int          ipv4_only;          /*!< Only do IPv4 */
static int          ipv6_only;          /*!< Only do IPv6 */

static const char  *tls_ca_path;        /*!< TLS verification path. */
static const char  *tls_cert;           /*!< TLS certificate filename. */
static const char  *tls_key;            /*!< TLS key filename. */

static const char  *server;             /*!< Host to connect to. */
static const char  *port;               /*!< Port to use. */

static const char  *from;               /*!< Sender address. */
static char       **to;                 /*!< Recipient addresses. */

static int          sock;               /*!< Communications socket. */
static SSL         *tls;                /*!< TLS connection state. */
static SSL_CTX     *tls_ctx;            /*!< TLS connection context. */

static struct auth *auth;               /*!< Authentication info. */
static int          halfarsed;          /*!< Old-fashioned SMTP. */
static int          smtp_error;         /*!< There has been an error. */
static int          started_tls;        /*!< TLS has been started. */

static int          pipe_active;        /*!< Pipelined command sequence. */
static int          pipe_count;         /*!< Number of commands. */
static int          pipe_size;          /*!< Size of following array. */
static struct {
	int         req;                /*!< Required status. */
	char        txt[5];             /*!< Abbreviated command text. */
}                  *pipe_cmd;

static struct buf   inbuf;
static struct buf   outbuf;

static char         command[BUF_SPACE];
static char         response[BUF_SPACE];

/**********************************************************************/

/*!
 * \brief Produce debugging output.
 */
static void
debug(int level, const char *fmt, ...)
{
	va_list ap;

	if(level > debug_level)
		return;

	va_start(ap, fmt);
	vwarnx(fmt, ap);
	va_end(ap);
}

/*!
 * \brief Copy characters between start and end to dst terminating
 * with a nul byte and never writing more than len bytes.
 */
static void
strlecpy(char *dst, size_t len, const char *start, const char *end)
{
	snprintf(dst, len, "%.*s", (int)(end - start), start);
}

/**********************************************************************/

/*!
 * \brief Check if the buffer is empty.
 */
static void
buf_fix(struct buf *buf)
{
	buf->space = buf->base + buf->size - buf->end;
	if(buf->end - buf->start > 0) {
		buf->used = buf->end - buf->start;
	} else {
		buf->start = buf->end = buf->base;
		buf->space = buf->size;
		buf->used = 0;
	}
}

/*!
 * \brief Ensure there is enough space in the buffer.
 */
static void
buf_require(struct buf *buf, size_t size)
{
	char *base;

	size += buf->used;
	if(buf->space >= size)
		return;
	if(buf->size == 0)
		buf->size = BUF_SPACE;
	while(size > buf->size)
		buf->size *= 2;
	base = malloc(buf->size);
	if(base == NULL)
		err(1, "malloc");
	size = buf->end - buf->start;
	memcpy(base, buf->start, size);
	free(buf->base);
	buf->start = buf->base = base;
	buf->end = base + size;
	buf_fix(buf);
}

/*!
 * \brief Update buffer after data has been added.
 */
static void
buf_add(struct buf *buf, size_t size)
{
	buf->end += size;
	buf_fix(buf);
}

/*!
 * \brief Update buffer after a number of bytes of data have been removed.
 */
static void
buf_use(struct buf *buf, size_t size)
{
	buf->start += size;
	buf_fix(buf);
}

/*!
 * \brief Update buffer after data has been removed up to a certain point.
 */
static void
buf_use_to(struct buf *buf, const char *ptr)
{
	assert(ptr >= buf->start && ptr <= buf->end);
	buf_use(buf, ptr - buf->start);
}

/*!
 * \brief Initialize a buffer.
 */
static void
buf_init(struct buf *buf)
{
	buf_require(buf, 0);
}

/*!
 * \brief Empty a buffer.
 */
static void
buf_clear(struct buf *buf)
{
	buf_use(buf, buf->used);
}

/**********************************************************************/

/*!
 * \brief Add a string to the buffer.
 */
static void
buf_add_str(struct buf *buf, const char *str)
{
	size_t len = strlen(str);
	buf_require(buf, len);
	memcpy(buf->end, str, len);
	buf_add(buf, len);
}

/*!
 * \brief Add a formatted string to the buffer using varargs.
 */
static void
buf_vprintf(struct buf *buf, const char *fmt, va_list ap)
{
	va_list apcp;
	size_t len;

	va_copy(apcp, ap);
	len = vsnprintf(NULL, 0, fmt, apcp);
	buf_require(buf, len);
	vsnprintf(buf->end, buf->space, fmt, ap);
	buf_add(buf, len);
}

/*!
 * \brief Add a formatted string to the buffer.
 */
static void
buf_printf(struct buf *buf, const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	buf_vprintf(buf, fmt, ap);
	va_end(ap);
}

/*!
 * \brief Read a line from a stream into the buffer.
 */
static int
buf_getline(struct buf *buf, FILE *stream)
{
	const char *start;
	int c;

	start = buf->end;
	while(c = getc(stream), c != EOF) {
		if(buf->space == 0)
			buf_require(buf, BUF_SPACE);
		if(c == '\n') {
			*buf->end = '\0';
			return(1);
		} else {
			*buf->end = c;
			buf_add(buf, 1);
		}
	}
	if(ferror(stream))
		err(1, "error reading input");
	*buf->end = '\0';
	return(buf->end != start);
}

/**********************************************************************/

/*!
 * \brief Report a TLS error.
 */
static void
tls_error(const char *function)
{
	errx(1, "%s: %s", function,
	    ERR_error_string(ERR_get_error(), NULL));
}

/*!
 * \brief Produce TLS debugging output.
 */
static void
tls_info_callback(const SSL *s, int where, int ret)
{
	where = where;
	ret = ret;
	debug(1, "TLS info: %s", SSL_state_string_long(s));
//	if(strstr(SSL_state_string_long(s), "read server done") != NULL) {
//		debug(1, "TLS timeout injection!");
//		sleep(1000);
//	}
}

/*!
 * \brief Set up TLS.
 */
static void
tls_init(void)
{
	SSL_library_init();
	SSL_load_error_strings();

	tls_ctx = SSL_CTX_new(SSLv23_client_method());
	if(tls_ctx == NULL)
		tls_error("SSL_CTX_new");
	SSL_CTX_set_info_callback(tls_ctx, tls_info_callback);
	if(!RAND_status())
		errx(1, "not enough TLS random seed data");

	if(tls_cert != NULL &&
	    !SSL_CTX_use_certificate_chain_file(tls_ctx, tls_cert))
		tls_error("SSL_CTX_use_certificate_chain_file");
	if(tls_key != NULL &&
	    !SSL_CTX_use_PrivateKey_file(tls_ctx, tls_key, SSL_FILETYPE_PEM))
		tls_error("SSL_CTX_use_PrivateKey_file");

	if(!SSL_CTX_set_default_verify_paths(tls_ctx))
		tls_error("SSL_CTX_set_default_verify_paths");
	if(tls_ca_path != NULL) {
		const char *file = NULL;
		const char *dir = NULL;
		struct stat st;
		if(stat(tls_ca_path, &st) < 0)
			err(1, "stat %s", tls_ca_path);
		if((st.st_mode & S_IFMT) == S_IFDIR)
			dir = tls_ca_path;
		else
			file = tls_ca_path;
		if(!SSL_CTX_load_verify_locations(tls_ctx, file, dir))
			tls_error("SSL_CTX_load_verify_locations");
	}
	debug(1, "TLS initialized");
}

/*!
 * \brief Start TLS.
 */
static void
tls_start(void)
{
	X509 *cert;
	long verified;

	tls = SSL_new(tls_ctx);
	if(tls == NULL)
		tls_error("SSL_new");
	SSL_set_session_id_context(tls, (const unsigned char *)"smtpc", 5);
	if(!SSL_set_fd(tls, sock))
		tls_error("SSL_set_fd");
	if(SSL_connect(tls) < 1)
		tls_error("SSL_connect");
	cert = SSL_get_peer_certificate(tls);
	if(cert != NULL) {
		debug(1, "TLS negotiated with %s",
		    X509_NAME_oneline(X509_get_subject_name(cert), NULL, 0));
		verified = SSL_get_verify_result(tls);
		debug(1, "TLS verification result: %s",
		    X509_verify_cert_error_string(verified));
		if(!tls_no_verify && verified != X509_V_OK)
			exit(1);
	} else {
		debug(1, "TLS verification result: no server certificate");
		if(!tls_no_verify)
			exit(1);
	}
	started_tls = 1;
}

/**********************************************************************/

/*!
 * \brief Read some stuff from the server.
 */
static void
smtp_read(void)
{
	ssize_t n;
	char *p;

	buf_require(&inbuf, BUF_SPACE);
	if(started_tls) {
		n = SSL_read(tls, inbuf.end, (int)inbuf.space);
		if(n < 0)
			tls_error("SSL_read");
		if(n == 0) {
			if(SSL_get_shutdown(tls))
				errx(1, "Unexpected TLS close");
			else
				tls_error("SSL_read");
		}
	} else {
		n = read(sock, inbuf.end, inbuf.space);
		if(n < 0)
			err(1, "read");
		if(n == 0)
			errx(1, "Unexpected connection close");
	}
	p = memchr(inbuf.end, '\0', n);
	if(p != NULL)
		errx(1, "garbage from server after: %.*s", (int)n, inbuf.end);
	buf_add(&inbuf, n);
	debug(2, "smtp_read buffer:\n%.*s", (int)inbuf.used, inbuf.start);
}

/*!
 * \brief Read an SMTP response.
 */
static int
smtp_get_response(void)
{
	char *p, *q, *r;
	int i, status;

	status = 0;

	p = inbuf.start;
	for(;;) {
		/* check line termination */
		r = memchr(p, '\r', inbuf.end - p);
		if(r == NULL || r == inbuf.end - 1) {
			smtp_read();
			p = inbuf.start; /* in case buffer moved */
			continue;
		}
		q = memchr(p, '\n', inbuf.end - p);
		if(q != r + 1)
			errx(1, "bad line termination in %.*s",
			    (int)(q < r ? q - p : r - p), p);
		debug(1, "< %.*s", (int)(r - p), p);

		/* check status code */
		i = 0;
		for(q = p; q - p < 3; q++) {
			if(*q < '0' || *q > '9')
				errx(1, "bad status code in %.*s",
				    (int)(r - p), p);
			i *= 10;
			i += *q - '0';
		}
		if(status == 0)
			status = i;
		else if(status != i)
			errx(1, "inconsistent status in %.*s",
			    (int)(r - p), p);

		/* end of response? */
		if(*q == ' ') {
			strlecpy(response, sizeof(response), inbuf.start, r);
			buf_use_to(&inbuf, r + 2);
			debug(2, "status %d", status);
			return(status);
		}
		if(*q != '-')
			errx(1, "bad continuation character in %.*s",
			    (int)(r - p), p);
		p = r + 2;
	}
}

/**********************************************************************/

/*!
 * \brief Send pending command(s) to the server.
 */
static void
smtp_flush(void)
{
	ssize_t n;

	debug(2, "smtp_flush buffer:\n%.*s", (int)outbuf.used, outbuf.start);
	if(started_tls) {
		n = SSL_write(tls, outbuf.start, (int)outbuf.used);
		if(n <= 0)
			tls_error("SSL_write");
	} else {
		n = write(sock, outbuf.start, outbuf.used);
		if(n < 0)
			err(1, "write");
	}
	buf_use(&outbuf, n);
	if(outbuf.used > 0)
		errx(1, "Unexpected short write");
}

/*!
 * \brief Say something to the SMTP server (internal version).
 */
static void
smtp_vprintf(const char *fmt, va_list ap)
{
	size_t offset;

	offset = outbuf.used;
	buf_vprintf(&outbuf, fmt, ap);
	strlecpy(command, sizeof(command),
	    outbuf.start + offset, outbuf.end);
	debug(1, "> %s", command);
	buf_add_str(&outbuf, "\r\n");
	if(pipe_active)
		return;
	smtp_flush();
}

/*!
 * \brief Say something to the SMTP server.
 */
static void
smtp_printf(const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	smtp_vprintf(fmt, ap);
	va_end(ap);
}

/**********************************************************************/

/*!
 * \brief Report an error and close the connection cleanly.
 */
static void
smtp_err(const char *fmt, ...)
{
	va_list ap;

	if(fmt != NULL) {
		va_start(ap, fmt);
		vwarnx(fmt, ap);
		va_end(ap);
		smtp_error = 1;
	}
	if(pipe_active)
		return;
	smtp_printf("QUIT");
	smtp_get_response();
	exit(1);
}

/*!
 * \brief Ensure the status matches what we expected.
 */
static int
smtp_check_status(int required, int status)
{
	void (*errfn)(const char *fmt, ...);
	char req[4];

	if(required < 0) {
		errfn = warnx;
		required = -required;
	} else {
		errfn = smtp_err;
	}
	if(required < 10) {
		if(required == status/100)
			return(1);
		snprintf(req, sizeof(req), "%dXX", required);
	} else
	if(required < 100) {
		if(required == status/10)
			return(1);
		snprintf(req, sizeof(req), "%dX", required);
	} else {
		if(required == status)
			return(1);
		snprintf(req, sizeof(req), "%d", required);
	}
	warnx("sent %s", command);
	warnx("rcvd %s", response);
	errfn("expected %s, got %d", req, status);
	return(0);
}

/*!
 * \brief Ensure we get the expected response.
 */
static int
smtp_check_response(int required)
{
	if(pipe_active != 1)
		return(smtp_check_status(required, smtp_get_response()));

	if(pipe_count == pipe_size) {
		if(pipe_size == 0)
			pipe_size = 4;
		else
			pipe_size *= 2;
		pipe_cmd = realloc(pipe_cmd, pipe_size);
		if(pipe_cmd == NULL)
			err(1, "malloc");
	}
	strncpy(pipe_cmd[pipe_count].txt, command, 4);
	pipe_cmd[pipe_count].txt[4] = '\0';
	pipe_cmd[pipe_count].req = required;
	pipe_count++;
	return(-1);
}

/*!
 * \brief Do a command-response-check operation.
 */
static int
smtp_cmd(int required, const char *fmt, ...)
{
	int ok;
	va_list ap;

	va_start(ap, fmt);
	smtp_vprintf(fmt, ap);
	ok = smtp_check_response(required);
	va_end(ap);

	return(ok);
}

/**********************************************************************/

/*!
 * \brief Start a group of pipelined commands.
 */
static void
smtp_pipe_start(void)
{
	if(pipeline && !halfarsed) {
		debug(1, "starting pipeline");
		pipe_active = 1;
		pipe_count = 0;
	}
}

/*!
 * \brief Finish a group of pipelined commands.
 */
static int
smtp_pipe_sync(void)
{
	static const char fmt[] = "%s (%i%s pipelined command)";
	static const char *th[] =
	    { "st", "nd", "rd", "th", "th",
	      "th", "th", "th", "th", "th" };
	int i, ok;

	if(!pipe_active)
		return(1);
	smtp_flush();
	pipe_active = 2;
	ok = 1;
	for(i = 0; i < pipe_count; i++) {
		buf_printf(&outbuf, fmt, pipe_cmd[i].txt, i+1, th[i%10]);
		strlecpy(command, sizeof(command), outbuf.start, outbuf.end);
		ok &= smtp_check_response(pipe_cmd[i].req);
		buf_clear(&outbuf);
	}
	pipe_active = 0;
	if(smtp_error)
		smtp_err(NULL);
	return(ok);
}

/**********************************************************************/

/*!
 * \brief Check for an ESMTP extension keyword.
 */
static const char *
smtp_extension(const char *keyword)
{
	const char *p, *q = response;
	size_t len = strlen(keyword);

	for(;;) {
		p = strcasestr(q, keyword);
		if(p == NULL)
			return(NULL);
		q = p + len;
		if(p < response + 4)
			continue;
		if(strncmp(p-4, "250-", 4) != 0 &&
		    strncmp(p-4, "250 ", 4) != 0)
			continue;
		if(*q != ' ' && *q != '\r' && *q != '\0')
			continue;
		return(q);
	}
}

/*!
 * \brief Check for an ESMTP extension parameter.
 */
static int
smtp_ext_param(const char *params, const char *wanted)
{
	const char *p, *q;
	const char *end;
	size_t len;

	if(params == NULL)
		return(0);
	q = params;
	end = strchr(params, '\r');
	len = strlen(wanted);
	for(;;) {
		p = strcasestr(q, wanted);
		if(p == NULL)
			return(0);
		q = p + len;
		if(q > end)
			return(0);
		if(*q != ' ' && *q != '\r' && *q != '\0')
			continue;
		return(1);
	}
}

/**********************************************************************/

static void
smtp_auth_respond(const unsigned char *resp, size_t len_resp)
{
	size_t len_resp64;
	/* more than enough space for base64 */
	buf_require(&outbuf, len_resp * 2);
	len_resp64 = b64_ntop(resp, len_resp, outbuf.end, outbuf.space);
	buf_add(&outbuf, len_resp64);
}

static void
smtp_auth(void)
{
	size_t len_chall64, len_resp;
	unsigned char *chall, *resp;
	const char *chall64;
	ssize_t len_chall;
	void *state;

	debug(1, "> AUTH %s ...", auth->method);
	buf_printf(&outbuf, "AUTH %s", auth->method);
	resp = NULL;
	len_resp = 0;
	if(auth_delay)
		state = NULL;
	else
		state = auth->function(NULL, NULL, 0, &resp, &len_resp);
	if(resp != NULL) {
		buf_add_str(&outbuf, " ");
		smtp_auth_respond(resp, len_resp);
		free(resp);
	}
	buf_add_str(&outbuf, "\r\n");
	smtp_flush();
	for(;;)
		switch(smtp_get_response()) {
		case(334):
			/* Size of base64 is more than enough space for binary. */
			chall64 = response + 4;
			len_chall64 = strlen(chall64);
			chall = malloc(len_chall64);
			if(chall == NULL)
				err(1, "malloc");
			len_chall = b64_pton(chall64, chall, len_chall64);
			if(len_chall < 0)
				smtp_err("SMTP AUTH protocol error: "
				    "bad base64 in challenge '%s'", chall64);
			chall[len_chall] = '\0';
			resp = NULL;
			len_resp = 0;
			state = auth->function(state,
			    chall, len_chall, &resp, &len_resp);
			smtp_auth_respond(resp, len_resp);
			buf_add_str(&outbuf, "\r\n");
			smtp_flush();
			free(chall);
			free(resp);
			break;
		case(235):
			return;
		default:
			smtp_err("SMTP AUTH %s failed: %s",
			    auth->method, response);
		}
}

#define SMTP_AUTH_RESPONSE(str, len) do {	\
	*resp = malloc(len);			\
	if(*resp == NULL)			\
		err(1, "malloc");		\
	memcpy(*resp, str, len);		\
	*len_resp = len;			\
} while(0);

/**********************************************************************/

static void *
auth_external(void *state,
    const unsigned char *chall, size_t len_chall,
    unsigned char **resp, size_t *len_resp)
{
	if(chall != NULL || len_chall != 0)
		smtp_err("AUTH EXTERNAL protocol error: unexpected challenge");
	SMTP_AUTH_RESPONSE(auth_username, auth_username_len);
	/* Keep no state. */
	return(state);
}

static void *
auth_login(void *state_v,
    const unsigned char *chall, size_t len_chall,
    unsigned char **resp, size_t *len_resp)
{
	static char base[] = "012";
	char *state = state_v ? state_v : base;

	len_chall = len_chall;
	debug(2, "AUTH LOGIN %d (%s)",
	    (int)(state - base), chall ? (const char *)chall : "-");
	switch(state - base) {
	case(0):
		/* Send no initial response. */
		break;
	case(1):
		SMTP_AUTH_RESPONSE(auth_username, auth_username_len);
		break;
	case(2):
		SMTP_AUTH_RESPONSE(auth_password, auth_password_len);
		break;
	default:
		smtp_err("AUTH LOGIN protocol error");
	}
	return(state + 1);
}

static void *
auth_plain(void *state,
    const unsigned char *chall, size_t len_chall,
    unsigned char **resp, size_t *len_resp)
{
	unsigned char *creds;
	size_t len;

	if(chall != NULL || len_chall != 0)
		smtp_err("AUTH PLAIN protocol error: unexpected challenge");
	/* Response is \0username\0password */
	*len_resp = len = auth_username_len + auth_password_len + 2;
	*resp = creds = malloc(len);
	if(creds == NULL)
		err(1, "malloc");
	*(creds) = '\0';
	memcpy(creds+1, auth_username, auth_username_len);
	*(creds+1+auth_username_len) = '\0';
	memcpy(creds+1+auth_username_len+1, auth_password, auth_password_len);
	/* Keep no state. */
	return(state);
}

static void *
auth_cram_md5(void *state,
    const unsigned char *chall, size_t len_chall,
    unsigned char **resp, size_t *len_resp)
{
	static const unsigned char hex[] = "0123456789abcdef";
	unsigned char hmac[MD5_DIGEST_LENGTH];
	unsigned char *creds, *creds_hmac;
	size_t i;

	/* Send no initial response. */
	if(chall == NULL || len_chall == 0)
		return(state);
	HMAC(EVP_md5(), auth_password, (int)auth_password_len,
	    chall, len_chall, hmac, NULL);
	/* Response is username SPACE hex-hmac */
	*len_resp = auth_username_len + 1 + sizeof(hmac) * 2;
	*resp = creds = malloc(*len_resp + 1);
	if(creds == NULL)
		err(1, "malloc");
	memcpy(creds, auth_username, auth_username_len);
	creds[auth_username_len] = ' ';
	creds_hmac = creds + auth_username_len + 1;
	for(i = 0; i < sizeof(hmac); i++) {
		creds_hmac[2 * i + 0] = hex[(hmac[i] >> 4) & 0xF];
		creds_hmac[2 * i + 1] = hex[(hmac[i] >> 0) & 0xF];
	}
	/* Keep no state. */
	return(state);
}

/**********************************************************************/

/*!
 * \brief A do-nothing signal handler.
 */
static void
no_op(int sig)
{
	sig = sig;
}

/*!
 * \brief Try to open a connection, handling timeouts.
 */
static int
addr_connect(const char *h, const char *p)
{
	int r, s;
	struct addrinfo ai_hints, *ai0, *ai;
	char addr[NS_MAXDNAME];

	debug(1, "looking up address %s:%s", h, p);
	memset(&ai_hints, 0, sizeof(ai_hints));
	ai_hints.ai_flags = AI_CANONNAME;
	ai_hints.ai_family = PF_UNSPEC;
	ai_hints.ai_socktype = SOCK_STREAM;
	r = getaddrinfo(h, p, &ai_hints, &ai0);
	if(r) {
		warnx("%s", gai_strerror(r));
		return(-1);
	}
	debug(1, "found %s", ai0->ai_canonname);
	for(ai = ai0; ai != NULL; ai = ai->ai_next) {
		getnameinfo(ai->ai_addr, ai->ai_addrlen,
		    addr, sizeof(addr), NULL, 0, NI_NUMERICHOST);
		debug(1, "found %s", addr);
	}
	s = -1;
	for(ai = ai0; ai != NULL; ai = ai->ai_next) {
		getnameinfo(ai->ai_addr, ai->ai_addrlen,
		    addr, sizeof(addr), NULL, 0, NI_NUMERICHOST);

		if (ipv4_only && ai->ai_family != PF_INET) {
			debug(1, "skipping %s", addr);
			continue;
		}
		if (ipv6_only && ai->ai_family != PF_INET6) {
			debug(1, "skipping %s", addr);
			continue;
		}

		debug(1, "connecting to %s", addr);
		s = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
		if(s < 0) {
			warn("socket");
			continue;
		}
		/* quicker connect timeout */
		alarm(timeout);
		if(connect(s, ai->ai_addr, ai->ai_addrlen) < 0) {
			warn("connect");
			close(s);
			s = -1;
			continue;
		}
		alarm(0);
		debug(1, "connected!");
		break;  /* okay we got one */
	}
	freeaddrinfo(ai0);
	return(s);
}

/*!
 * \brief Compare MX records in a DNS response for sorting.
 */
static int
mx_compare(const void *a, const void *b)
{
	unsigned char *aa, *bb;
	int aaa, bbb;
	aa = *(unsigned char *const *)a;
	bb = *(unsigned char *const *)b;
	NS_GET16(aaa, aa);
	NS_GET16(bbb, bb);
	return(aaa - bbb);
}

/*!
 * \brief Look up MX records and to connect to one of the
 * resulting hosts, trying them in order of priority.
 */
static int
mx_connect(const char *dom, const char *p, int depth)
{
	int i, s, t, anslen, namelen, rrlen;
	unsigned char *ptr, **rrset;
	unsigned char ans[NS_MAXDNAME*10];
	char name[NS_MAXDNAME];
	ns_msg *h;

	if(depth < 0) {
		warnx("CNAME recursion too deep");
		return(-1);
	}
	debug(1, "looking up MX %s", dom);
	anslen = res_query(dom, ns_c_in, ns_t_mx, ans, sizeof(ans));
	if(anslen < 0)
		switch(h_errno) {
		case(HOST_NOT_FOUND):
		case(NO_DATA):
			warnx("MX lookup: %s", hstrerror(h_errno));
			/* fall back to A lookup */
			return(-2);
		case(TRY_AGAIN):
		case(NO_RECOVERY):
			errx(1, "MX lookup: %s", hstrerror(h_errno));
		default:
			err(1, "unknown DNS error %d", h_errno);
		}
	h = (ns_msg *)ans;
	ptr = ans + sizeof(h);
	/* skip over the query part */
	for(i = ntohs(ns_msg_count(*h, ns_s_qd)); i > 0; i--) {
		namelen = dn_expand(ans, ans + anslen, ptr,
		    name, sizeof(name));
		if(namelen < 0) {
			warnx("error parsing MX query");
			return(-1);
		}
		/* skip name & type & class */
		ptr += namelen + 4;
	}
	/* create an index of the answer part */
	rrlen = ntohs(ns_msg_count(*h, ns_s_an));
	rrset = malloc(rrlen * sizeof(*rrset));
	if(rrset == NULL)
		err(1, "malloc");
	for(i = 0; i < rrlen; i++) {
		namelen = dn_expand(ans, ans + anslen, ptr,
		    name, sizeof(name));
		if(namelen < 0) {
			warnx("error parsing MX answer");
			return(-1);
		}
		ptr += namelen;
		NS_GET16(t, ptr);
		if(t != ns_t_mx && t != ns_t_cname) {
			warnx("MX answer type mismatch");
			return(-1);
		}
		/* skip class, TTL, data length */
		ptr += 8;
		rrset[i] = ptr;
		/* print debugging output of data */
		if(t == ns_t_cname)
			s = 0;
		else
			NS_GET16(s, ptr);
		namelen = dn_expand(ans, ans + anslen, ptr,
		    name, sizeof(name));
		if(namelen < 0) {
			warnx("error parsing %s target",
			    t == ns_t_cname ? "CNAME" : "MX");
			return(-1);
		}
		if(t == ns_t_cname) {
			debug(1, "CNAME %s", name);
			return(mx_connect(name, p, depth-1));
		} else {
			debug(1, "MX %d %s", s, name);
		}
		ptr += namelen;
	}
	qsort(rrset, rrlen, sizeof(*rrset), mx_compare);
	/* try connecting to each host in turn */
	for(i = mx-1; i < rrlen; i++) {
		namelen = dn_expand(ans, ans + anslen, rrset[i] + 2,
		    name, sizeof(name));
		s = addr_connect(name, p);
		if(s >= 0) {
			free(rrset);
			return(s);
		}
	}
	free(rrset);
	return(-1);
}

/*!
 * \brief Explain command line options.
 */
static void
usage(void)
{
	fprintf(stderr,
	    "usage: %s [-dhpsS] [-a m:u:p] [-m [N]] [-t timeout] \\\n"
	    "			[-A f|d] [-C c:k] [-H hostname] \\\n"
	    "			<server>[:port] <from> <to>...\n"
	    "	-a	Use AUTH method:username:password\n"
	    "	-d	Increase debugging level\n"
	    "	-h	Greet the server with HELO\n"
	    "	-m	Connect to Nth (1st) MX record\n"
	    "	-p	Try SMTP pipelining\n"
	    "	-s	Use TLS (more than once for TLS on connect)\n"
	    "	-t	Connect timeout\n"
	    "	-v	Verify addresses (more than once to do callout)\n"
	    "	-A	TLS certificate authority file or directory\n"
	    "	-C	TLS client cert:key\n"
	    "	-H	Hostname for EHLO argument\n"
	    "	-S	Skip TLS server certificate verification\n"
	    "	-4	Only connect over IPv4\n"
	    "	-6	Only connect over IPv6\n",
	    progname);
	exit(2);
}

/*!
 * \brief The main program.
 */
int
main(int argc, char *argv[])
{
	int c, r;
	const char *p;
	struct sigaction sa;

	progname = strrchr(argv[0], '/');
	if(!progname) progname = argv[0];
	else progname += 1;

	if(gethostname(hostname, sizeof(hostname)) < 0)
		err(1, "gethostname");

	while((c = getopt(argc, argv, "a:dhm:pst:vA:C:H:S64")) != -1)
		switch(c) {
		case('a'):	/* AUTH parameters */
			if(optarg[0] == ':') {
				auth_delay = 1;
				optarg += 1;
			}
			auth_method = strsep(&optarg, ":");
			auth_username = strsep(&optarg, ":");
			auth_password = optarg;
			break;
		case('d'):      /* Debugging */
			debug_level++;
			break;
		case('h'):      /* HELO */
			halfarsed++;
			break;
		case('m'):      /* Use MX records. */
			mx = atoi(optarg);
			if(mx < 1)
				mx = 1;
			break;
		case('p'):      /* Try SMTP pipelining. */
			pipeline++;
			break;
		case('s'):	/* TLS */
			use_tls++;
			break;
		case('t'):	/* Connection timeout. */
			timeout = atoi(optarg);
			break;
		case('v'):	/* Verify address(es) */
			verify++;
			break;
		case('A'):	/* CA certificate path. */
			tls_ca_path = optarg;
			break;
		case('C'):	/* Certificate + key */
			tls_cert = strsep(&optarg, ":");
			tls_key = optarg;
			break;
		case('H'):      /* Hostname */
			snprintf(hostname, sizeof(hostname), "%s", optarg);
			break;
		case('S'):	/* No TLS server cert verification. */
			tls_no_verify++;
			break;
		case('4'):
			ipv4_only = 1;
			break;
		case('6'):
			ipv6_only = 1;
			break;
		default:
			usage();
		}
	argc -= optind;
	argv += optind;

	if(argc < 2)
		usage();

	if(auth_method != NULL) {
		for(auth = auth_table; auth->method != NULL; auth++)
			if(strcasecmp(auth->method, auth_method) == 0)
				break;
		if(auth->method == NULL)
			errx(1, "SMTP AUTH %s not supported", auth_method);
		if(auth_username == NULL) {
			uid_t uid = getuid();
			struct passwd *pw = getpwuid(uid);
			if(pw != NULL)
				auth_username = strdup(pw->pw_name);
			if(auth_username == NULL)
				err(1, "could not get username");
		}
		if(auth_password == NULL)
			auth_password = getpass("Password: ");
		auth_username_len = strlen(auth_username);
		auth_password_len = strlen(auth_password);
	}

	if(verify > 2) {
		if(mx < 1)
			mx = 1;
		server = strchr(argv[1], '@');
		if(server == NULL)
			errx(1, "Missing @ in email address");
		server++;
		port = "smtp";
		from = argv[0];
		to = argv + 1;
	} else {
		server = strsep(&argv[0], ":");
		port = (argv[0] == NULL) ? "smtp" : argv[0];
		if(verify == 1) {
			to = argv + 1;
		} else {
			from = argv[1];
			to = argv + 2;
		}
	}

	/* Make SIGALRM stop the current system call. */
	memset(&sa, 0, sizeof(sa));
	sa.sa_handler = no_op;
	r = sigaction(SIGALRM, &sa, NULL);
	if(r < 0)
		err(1, "sigaction SIGALRM");

	sock = -1;
	if(mx) {
		sock = mx_connect(server, port, 5);
		if(sock == -1)
			exit(1);
		/* if(sock == -2) fall back to A lookup */
	}
	if(sock < 0)
		sock = addr_connect(server, port);
	if(sock < 0)
		errx(1, "could not connect to %s:%s", server, port);

	/* Do TLS and buffer initialization. */
	if(use_tls > 0)
		tls_init();
	if(use_tls > 1)
		tls_start();
	buf_init(&outbuf);

	/* Now for some SMTP. */
	snprintf(command, sizeof(command), "initial connection");
	smtp_check_response(220);
helo:
	r = 500;
	/* We can become halfarsed after starting TLS. */
	if(!halfarsed || (use_tls && !started_tls)) {
		smtp_printf("EHLO %s", hostname);
		r = smtp_get_response();
	}
	if(r/100 == 5) {
		halfarsed++;
		smtp_cmd(250, "HELO %s", hostname);
	} else {
		/* Check service extensions. */
		smtp_check_status(250, r);
		if(smtp_extension("PIPELINING") == NULL) {
			debug(1, "PIPELINING not supported");
			pipeline = 0;
		}
		/* We could just skip this and find the error later... */
		if(use_tls && !started_tls &&
		    smtp_extension("STARTTLS") == NULL)
			smtp_err("STARTTLS not supported");
		if(auth != NULL) {
			p = smtp_extension("AUTH");
			if(!smtp_ext_param(p, auth_method)
			    && (!use_tls || started_tls))
				smtp_err("SMTP AUTH %s not supported",
				    auth_method);
		}
	}
	/* Do security things. */
	if(use_tls && !started_tls) {
		smtp_cmd(220, "STARTTLS");
		tls_start();
		goto helo;
	}
	if(auth != NULL)
		smtp_auth();
	/* now for the actual work */
	if(verify) {
		int status = 0;
		while(*to != NULL) {
			if(verify > 1) {
				smtp_pipe_start();
				smtp_cmd(250, "MAIL FROM:<%s>", from);
				r = smtp_cmd(-25, "RCPT TO:<%s>", *to);
				smtp_cmd(250, "RSET");
				r &= smtp_pipe_sync();
			} else {
				r = smtp_cmd(-25, "VRFY %s", *to);
			}
			if(r)
				warnx("verified %s", *to);
			else
				status = 1;
			to++;
		}
		smtp_cmd(221, "QUIT");
		return(status);
	} else {
		/* Send a message. */
		smtp_pipe_start();
		smtp_cmd(250, "MAIL FROM:<%s>", from);
		while(*to != NULL)
			smtp_cmd(-25, "RCPT TO:<%s>", *to++);
		smtp_cmd(354, "DATA");
		smtp_pipe_sync();
		for(;;) {
			/* assume that we need to stuff in a dot */
			buf_add_str(&outbuf, ".");
			if(buf_getline(&outbuf, stdin) == 0)
				break;
			buf_add_str(&outbuf, "\r\n");
			/* unstuff if we didn't need it after all */
			if(outbuf.start[1] != '.')
				buf_use(&outbuf, 1);
			smtp_flush();
		}
		buf_add_str(&outbuf, "\r\n");
		smtp_flush();
		smtp_check_response(250);
		smtp_cmd(221, "QUIT");
		return(0);
	}
}

/* EOF smtpc/main.c */
