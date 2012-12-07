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

#define c_closed cstate == CLOSED
#define c_listen cstate == LISTEN
#define c_syn_sent cstate == SYN_SENT
#define c_syn_received cstate == SYN_RECEIVED
#define c_established cstate == ESTABLISHED
#define c_fin_wait_1 cstate == FIN_WAIT_1
#define c_fin_wait_2 cstate == FIN_WAIT_2
#define c_close_wait cstate == CLOSE_WAIT
#define c_closing cstate == CLOSING
#define c_last_ack cstate == LAST_ACK
#define c_time_wait cstate == TIME_WAIT

#define s_closed sstate == CLOSED
#define s_listen sstate == LISTEN
#define s_syn_sent sstate == SYN_SENT
#define s_syn_received sstate == SYN_RECEIVED
#define s_established sstate == ESTABLISHED
#define s_fin_wait_1 sstate == FIN_WAIT_1
#define s_fin_wait_2 sstate == FIN_WAIT_2
#define s_close_wait sstate == CLOSE_WAIT
#define s_closing sstate == CLOSING
#define s_last_ack sstate == LAST_ACK
#define s_time_wait sstate == TIME_WAIT

mtype = {
      SYN,
      FIN,
      ACK,
      RST,
      SYN_ACK,
      FIN_ACK,
      DATA
}

/* 
   c?FOO,ack,eval(seq);  // their ack should anticipate your next message
   ack++;                // only if FOO <> ACK

   c!BAR,ack,seq;
   seq++;                // only if BAR <> ACK
 */

/*                       CTL    SEQ  ACK */
chan toclient = [1] of { mtype, int, int }
chan toserver = [1] of { mtype, int, int }

int s_listen = 1;
int s_connect = 0;
int s_close = 1;
int c_connect = 1;
int c_close = 0;
int c_rst = 0;
int c_send = 0;
int c_timeout = 1;
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

  /* initial connection */
  (c_connect);
  printf("c: initial connection\n");
  toserver!SYN,seq,0;
  printf("--> SYN %d %d\n", seq, ack);
  seq++;
  goto syn_sent;

  listen:
    cstate = LISTEN;
    printf("c: listen %d\n", seq);
    if
    :: (c_close) ->
       goto closed;
    :: (c_send) ->
       printf("--> SYN %d %d\n", seq, ack);
       toserver!SYN,seq,ack;
       seq++;
       goto syn_sent;
    fi;

  syn_sent:
    cstate = SYN_SENT;
    printf("c: syn_sent %d\n", seq);
    if
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == SYN_ACK || msg == SYN);
       if
       :: (msg == SYN_ACK) ->
          ack = inseq + 1;
          printf("--> ACK %d %d\n", seq, ack);
          toserver!ACK,seq,ack;
          goto established;
       :: (msg == SYN) ->
          ack = inseq + 1;
          printf("--> SYN_ACK %d %d\n", seq, ack);
          toserver!SYN_ACK,seq,ack;
          seq = seq + 1;
          goto syn_received;
       fi;
    :: (c_close) ->
       goto closed;
    fi;
    
  syn_received:
    cstate = SYN_RECEIVED;
    printf("c: syn_received %d\n", seq);
    if
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == RST);
       ack = inseq + 1;
       goto listen;
    :: (c_close) ->
       printf("--> FIN %d %d\n", seq, ack);
       toserver!FIN,seq,ack;
       seq++;
       goto fin_wait_1;
    fi;
    
  established:
    cstate = ESTABLISHED;
    printf("c: established %d\n", seq);
    if
    :: (c_close) ->
       printf("--> FIN %d %d\n", seq, ack);
       toserver!FIN,seq,ack;
       seq++;
       goto fin_wait_1;
    :: else ->
       printf ("--> DATA %d %d\n", seq, ack);
       toserver!DATA,seq,ack;
       l_msg = DATA; l_seq = seq; l_ack = ack;
       seq++;
       if
       :: toclient?msg,inseq,inack ->
          assert(inack == seq);
          assert(msg == ACK);
          ack = inseq;
          c_close = 1;
          goto established;
       :: timeout ->
          printf("resending\n");
          toserver!l_msg,l_seq,l_ack;
          goto established;
       fi;
    :: timeout ->
       printf("!!!!!TIMEOUT!!!!!\n");
       toserver!l_msg,l_seq,l_ack;
       goto established;
    fi;
    goto closed;
    
  fin_wait_1:
    cstate = FIN_WAIT_1;
    printf("c: fin_wait_1 %d\n", seq);
    if
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == ACK || msg == FIN);
       if
       :: (msg == ACK) ->
          ack = inseq;
          goto fin_wait_2;
       :: (msg == FIN) ->
          ack = inseq + 1;
          toserver!ACK,seq,ack;
          goto closing;
       :: (msg == FIN) ->
          ack = inseq + 1;
          toserver!FIN_ACK,seq,ack;
          seq++;
          goto time_wait;
       fi;
    fi;
    
  fin_wait_2:
    cstate = FIN_WAIT_2;
    printf("c: fin_wait_2 %d\n", seq);
    if
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == FIN);
       ack = inseq + 1;
       toserver!ACK,seq,ack;
       goto time_wait;
    fi;

  close_wait:
    cstate = CLOSE_WAIT;
    printf("c: close_wait %d\n", seq);
    
  closing:
    cstate = CLOSING;
    printf("c: closing %d\n", seq);
    if
    :: toclient?msg,inseq,inack ->
       assert(inack == seq);
       assert(msg == ACK);
       goto time_wait;
    :: timeout ->
       assert(0);
    fi;

  last_ack:
    cstate = LAST_ACK;
    printf("c: last_ack %d\n", seq);
    
  time_wait:
    cstate = TIME_WAIT;
    printf("c: time_wait %d\n", seq);
    if
    :: (c_timeout) -> 
       toserver!ACK,ack,seq;
       goto closed;
    fi;

  closed:
    cstate = CLOSED;
    printf("c: closed %d\n", seq);
    
}

proctype Server ()
{
  mtype ctl;
  int seq = 300;
  int ack = 0;
  int null;

  int l_msg;
  int l_seq;
  int l_ack;

  if
  :: (s_listen);
     goto listen;
  :: (s_connect);
     printf("<-- %d %d\n", seq, ack);
     toclient!SYN,seq,ack;
     seq++;
     goto syn_sent;
  fi;

  listen:
    sstate = LISTEN;
    printf("s: listen %d\n", seq);
    if
    :: toserver?SYN,ack,null ->
       ack++;
       printf("<-- SYN_ACK %d %d\n", seq, ack);
       toclient!SYN_ACK,seq,ack;
       seq++;
       goto syn_received;
    fi;

  syn_sent:
    sstate = SYN_SENT;
    printf("s: syn_sent %d\n", seq);
    if
    :: toserver?SYN,ack,null ->
       ack++;
       printf("<-- SYN_ACK %d %d\n", seq, ack);
       toclient!SYN_ACK,seq,ack;
       seq++;
       goto established;
    fi;
    
  syn_received:
    sstate = SYN_RECEIVED;
    printf("s: syn_received %d\n", seq);
    if
    :: toserver?ACK,ack,eval(seq) ->
       goto established;
    fi;
    
  established:
    sstate = ESTABLISHED;
    printf("s: established %d\n", seq);
    if
    :: toserver?FIN,ack,eval(seq) ->
       ack++;
       toclient!ACK,seq,ack;
       goto close_wait;
    :: toserver?DATA,ack,eval(seq) ->
       printf("got data: %d\n", ack);
       ack++;
       printf("<-- ACK %d %d\n", seq, ack);
       toclient!ACK,seq,ack;
       goto established;
    :: timeout ->
       toserver!l_msg,l_seq,l_ack;
       goto established;
    fi;
    
  fin_wait_1:
    sstate = FIN_WAIT_1;
    printf("s: fin_wait_1 %d\n", seq);
    
  fin_wait_2:
    sstate = FIN_WAIT_2;
    printf("s: fin_wait_2 %d\n", seq);
    
  close_wait:
    sstate = CLOSE_WAIT;
    printf("s: close_wait %d\n", seq);
    if
    :: (s_close) ->
       toclient!FIN,seq,ack;
       seq++;
       goto last_ack;
    fi;
    
  closing:
    sstate = CLOSING;
    printf("s: closing %d\n", seq);
    
  last_ack:
    sstate = LAST_ACK;
    printf("s: last_ack %d\n", seq);
    if
    :: toserver?ACK,ack,seq;
       goto closed;
    fi;
    
  time_wait:
    sstate = TIME_WAIT;
    printf("s: time_wait %d\n", seq);

  closed:
    sstate = CLOSED;
    printf("s: closed %d\n", seq);
    
}

init
{
  run Client();
  run Server();
}
never  {    /* c_close_wait */
accept_init:
T0_init:
	if
	:: ((c_close_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_last_ack */
accept_init:
T0_init:
	if
	:: ((c_last_ack)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* s_fin_wait_1 */
accept_init:
T0_init:
	if
	:: ((s_fin_wait_1)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* s_fin_wait_2 */
accept_init:
T0_init:
	if
	:: ((s_fin_wait_2)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* s_closing */
accept_init:
T0_init:
	if
	:: ((s_closing)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* s_time_wait */
accept_init:
T0_init:
	if
	:: ((s_time_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* cclosed */
accept_init:
T0_init:
	if
	:: ((cclosed)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* sclosed */
accept_init:
T0_init:
	if
	:: ((sclosed)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_time_wait */
accept_init:
T0_init:
	if
	:: ((c_time_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_time_wait */
accept_init:
T0_init:
	if
	:: ((c_time_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_time_wait */
accept_init:
T0_init:
	if
	:: ((c_time_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_fin_wait_2 */
accept_init:
T0_init:
	if
	:: ((c_fin_wait_2)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_fin_wait_1 */
accept_init:
T0_init:
	if
	:: ((c_fin_wait_1)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_fin_wait_1 */
accept_init:
T0_init:
	if
	:: ((c_fin_wait_1)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* c_established_connection */
accept_init:
T0_init:
	if
	:: ((c_established_connection)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* s_last_ack */
accept_init:
T0_init:
	if
	:: ((s_last_ack)) -> goto accept_all
	fi;
accept_all:
	skip
}
never  {    /* s_close_wait */
accept_init:
T0_init:
	if
	:: ((s_close_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}
