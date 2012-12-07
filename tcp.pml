/* The state of each process is represented by one of these values. */
#define CLOSED        0
#define LISTEN        1
#define SYN_SENT      2
#define SYN_RECEIVED  3
#define ESTABLISHED   4
#define FIN_WAIT_1    5
#define FIN_WAIT_2    6
#define CLOSE_WAIT    7
#define CLOSING       8
#define LAST_ACK      9
#define TIME_WAIT     10
#define EXIT          11

/* These are all for use by LTL assertions. */
#define c_closed (cstate == CLOSED)
#define c_listen (cstate == LISTEN)
#define c_syn_sent (cstate == SYN_SENT)
#define c_syn_received (cstate == SYN_RECEIVED)
#define c_established (cstate == ESTABLISHED)
#define c_fin_wait_1 (cstate == FIN_WAIT_1)
#define c_fin_wait_2 (cstate == FIN_WAIT_2)
#define c_close_wait (cstate == CLOSE_WAIT)
#define c_closing (cstate == CLOSING)
#define c_last_ack (cstate == LAST_ACK)
#define c_time_wait (cstate == TIME_WAIT)
#define c_exit (cstate == EXIT)
#define s_closed (sstate == CLOSED)
#define s_listen (sstate == LISTEN)
#define s_syn_sent (sstate == SYN_SENT)
#define s_syn_received (sstate == SYN_RECEIVED)
#define s_established (sstate == ESTABLISHED)
#define s_fin_wait_1 (sstate == FIN_WAIT_1)
#define s_fin_wait_2 (sstate == FIN_WAIT_2)
#define s_close_wait (sstate == CLOSE_WAIT)
#define s_closing (sstate == CLOSING)
#define s_last_ack (sstate == LAST_ACK)
#define s_time_wait (sstate == TIME_WAIT)
#define s_exit (sstate == EXIT)

mtype = {
      SYN,
      FIN,
      ACK,
      RST,
      SYN_ACK,
      FIN_ACK,
      DATA
};

/* 
 * Instead of manually constructing a packet, we use a simple three-part
 * message to represent the content of a TCP message. The first part is the
 * type of signal, the second is the local sequence number, and the third is
 * the ack for the remote host.
 */

/*                       CTL    SEQ  ACK */
chan toclient = [1] of { mtype, int, int };
chan toserver = [1] of { mtype, int, int };

/* 
 * These are not messages from the socket, but from the environment (e.g. the
 * hypothetical program using the connection).
 */
int s_do_listen = 1;
int s_do_connect = 0;
int s_do_close = 1;
int s_do_exit = 0;
int c_do_connect = 1;
int c_do_close = 0;
int c_do_exit = 0;
int c_do_rst = 0;
int c_do_send = 0;
int c_timeout = 1;

/* 
 * Variables for assertions/debugging that record the abstract state of each
 * process.
 */
int sstate, cstate;

proctype Client ()
{
  mtype ctl;
  int seq = 100;
  int ack = 0;
  int null;

  int msg,inseq,inack;

  int l_msg;
  int l_seq;
  int l_ack;

  closed:
    cstate = CLOSED;
    printf("c: closed %d\n", seq);

    if

    /* connect / SYN -> syn_sent */
    :: (c_do_connect) ->
       c_do_connect = 0;
       printf("c: initial connection\n");
       toserver!SYN,seq,0;
       printf("--> SYN %d %d\n", seq, ack);
       seq++;
       goto syn_sent;
    :: (c_do_exit) ->
       goto exit;
    fi;
    assert(false);

  listen:
    cstate = LISTEN;
    printf("c: listen %d\n", seq);
    if

    /* close / -- -> closed*/
    :: (c_do_close) ->
       goto closed;

    /* send / SYN -> syn_sent */
    :: (c_do_send) ->
       printf("--> SYN %d %d\n", seq, ack);
       toserver!SYN,seq,ack;
       seq++;
       goto syn_sent;
    fi;
    assert(false);

  syn_sent:
    cstate = SYN_SENT;
    printf("c: syn_sent %d\n", seq);
    if
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == SYN_ACK || msg == SYN);
       if

       /* SYN + ACK / ACK -> established*/
       :: (msg == SYN_ACK) ->
          ack = inseq + 1;
          printf("--> ACK %d %d\n", seq, ack);
          toserver!ACK,seq,ack;
          goto established;

       /* SYN / SYN + ACK -> syn_received */
       :: (msg == SYN) ->
          ack = inseq + 1;
          printf("--> SYN_ACK %d %d\n", seq, ack);
          toserver!SYN_ACK,seq,ack;
          seq = seq + 1;
          goto syn_received;
       fi;
    :: (c_do_close) ->
       goto closed;
    fi;
    assert(false);
    
  syn_received:
    cstate = SYN_RECEIVED;
    printf("c: syn_received %d\n", seq);
    if

    /* RST / -- -> listen */
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == RST);
       ack = inseq + 1;
       goto listen;

    /* close / FIN -> fin_wait_1 */
    :: (c_do_close) ->
       printf("--> FIN %d %d\n", seq, ack);
       toserver!FIN,seq,ack;
       seq++;
       goto fin_wait_1;
    fi;
    assert(false);
    
  established:
    cstate = ESTABLISHED;
    printf("c: established %d\n", seq);
    if

    /* close / FIN -> fin_wait_1 */
    :: (c_do_close) ->
       printf("--> FIN %d %d\n", seq, ack);
       toserver!FIN,seq,ack;
       seq++;
       goto fin_wait_1;

    /* -- / DATA */
    :: else ->
       printf ("--> DATA %d %d\n", seq, ack);
       toserver!DATA,seq,ack;
       l_msg = DATA; l_seq = seq; l_ack = ack;
       seq++;
       if

       /* ACK / -- -> established */
       :: toclient?msg,inseq,inack ->
          assert(inack == seq);
          assert(msg == ACK);
          ack = inseq;
          c_do_close = 1;
          goto established;

       /* resend on timeout -> established */
       :: timeout ->
          printf("resending\n");
          toserver!l_msg,l_seq,l_ack;
          goto established;
       fi;
    fi;
    assert(false);
    
  fin_wait_1:
    cstate = FIN_WAIT_1;
    printf("c: fin_wait_1 %d\n", seq);
    if
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == ACK || msg == FIN);
       if

       /* ACK / -- -> fin_wait_2 */
       :: (msg == ACK) ->
          ack = inseq;
          goto fin_wait_2;

       /* FIN / ACK -> closing */
       :: (msg == FIN) ->
          ack = inseq + 1;
          toserver!ACK,seq,ack;
          goto closing;

       /* FIN / FIN + ACK -> time_wait */
       :: (msg == FIN) ->
          ack = inseq + 1;
          toserver!FIN_ACK,seq,ack;
          seq++;
          goto time_wait;
       fi;
    fi;
    assert(false);
    
  fin_wait_2:
    cstate = FIN_WAIT_2;
    printf("c: fin_wait_2 %d\n", seq);
    if

    /* FIN / ACK -> time_wait */
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == FIN);
       ack = inseq + 1;
       toserver!ACK,seq,ack;
       goto time_wait;
    fi;
    assert(false);

  close_wait:
    cstate = CLOSE_WAIT;
    printf("c: close_wait %d\n", seq);
    assert(false);
    
  closing:
    cstate = CLOSING;
    printf("c: closing %d\n", seq);
    if

    /* ACK / -- -> time_wait */
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == ACK);
       goto time_wait;
    fi;
    assert(false);

  last_ack:
    cstate = LAST_ACK;
    printf("c: last_ack %d\n", seq);
    assert(false);
    
  time_wait:
    cstate = TIME_WAIT;
    printf("c: time_wait %d\n", seq);
    if

    /* timeout / ACK -> closed */
    :: (c_timeout) -> 
       toserver!ACK,ack,seq;
       goto closed;
    fi;
    assert(false);

  exit:
    cstate = EXIT;
    printf("c: exit %d %d\n", seq, ack);
}

proctype Server ()
{
  mtype ctl;
  int seq = 300;
  int ack = 0;
  int null;

  int msg, inseq, inack;

  int l_msg;
  int l_seq;
  int l_ack;

  closed:
    sstate = CLOSED;
    printf("s: closed %d\n", seq);
    
    if

    /* list / -- */
    :: (s_do_listen) ->
       s_do_listen = 0;
       goto listen;

    /* connect / SYN */
    :: (s_do_connect) ->
       s_do_connect = 0;
       printf("<-- %d %d\n", seq, ack);
       toclient!SYN,seq,ack;
       seq++;
       goto syn_sent;

    :: (s_do_exit) ->
       goto exit;
    fi;
    assert(false);

  listen:
    sstate = LISTEN;
    printf("s: listen %d\n", seq);
    if

    /* SYN / SYN + ACK */
    :: toserver?msg,inseq,inack ->
       assert(msg == SYN);
       ack = inseq + 1;
       printf("<-- SYN_ACK %d %d\n", seq, ack);
       toclient!SYN_ACK,seq,ack;
       seq++;
       goto syn_received;
    fi;
    assert(false);

  syn_sent:
    sstate = SYN_SENT;
    printf("s: syn_sent %d\n", seq);
    if

    /* SYN / SYN + ACK */
    :: toserver?msg,inseq,inack ->
       assert(msg == SYN);
       ack = inseq + 1;
       printf("<-- SYN_ACK %d %d\n", seq, ack);
       toclient!SYN_ACK,seq,ack;
       seq++;
       goto established;
    fi;
    assert(false);
    
  syn_received:
    sstate = SYN_RECEIVED;
    printf("s: syn_received %d\n", seq);
    if

    /* ACK / -- */
    :: toserver?msg,inseq,inack ->
       assert(msg == ACK);
       assert(inack == seq);
       ack = inseq;
       goto established;
    fi;
    assert(false);
    
  established:
    sstate = ESTABLISHED;
    printf("s: established %d\n", seq);
    if
    :: toserver?msg,inseq,inack ->
       assert(msg == FIN || msg == DATA);
       assert(inack == seq);
       ack = inseq + 1;
       if

       /* FIN / ACK */
       :: (msg == FIN) ->
          toclient!ACK,seq,ack;
          goto close_wait;

       /* data / ACK */
       :: (msg == DATA) ->
          printf("got data: %d\n", ack - 1);
          printf("<-- ACK %d %d\n", seq, ack);
          toclient!ACK,seq,ack;
          goto established;
       fi;

    /* resend on timeout */
    :: timeout ->
       toserver!l_msg,l_seq,l_ack;
       goto established;
    fi;
    assert(false);
    
  fin_wait_1:
    sstate = FIN_WAIT_1;
    printf("s: fin_wait_1 %d\n", seq);
    assert(false);
    
  fin_wait_2:
    sstate = FIN_WAIT_2;
    printf("s: fin_wait_2 %d\n", seq);
    assert(false);
    
  close_wait:
    sstate = CLOSE_WAIT;
    printf("s: close_wait %d\n", seq);
    if

    /* close / FIN */
    :: (s_do_close) ->
       toclient!FIN,seq,ack;
       seq++;
       goto last_ack;
    fi;
    assert(false);
    
  closing:
    sstate = CLOSING;
    printf("s: closing %d\n", seq);
    assert(false);
    
  last_ack:
    sstate = LAST_ACK;
    printf("s: last_ack %d\n", seq);
    if

    /* ACK / -- */
    :: toserver?msg,inseq,inack;
       assert(msg == ACK);
       assert(inack == seq);
       ack = inseq;
       goto closed;
    fi;
    assert(false);
    
  time_wait:
    sstate = TIME_WAIT;
    printf("s: time_wait %d\n", seq);
    assert(false);

  exit:
    sstate = EXIT;
    printf("s: exit %d %d\n", seq, ack);
}

init
{
  run Client();
  run Server();
}
