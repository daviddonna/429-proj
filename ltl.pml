/* states that should never happen */

/* LTL_01 */
never {    /* c_close_wait
 */
accept_init:
T0_init:
	if
	:: ((c_close_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_02 */
never {    /* c_last_ack
 */
accept_init:
T0_init:
	if
	:: ((c_last_ack)) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_03 */
never {    /* s_fin_wait_1
 */
accept_init:
T0_init:
	if
	:: ((s_fin_wait_1)) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_04 */
never {    /* s_fin_wait_2
 */
accept_init:
T0_init:
	if
	:: ((s_fin_wait_2)) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_05 */
never {    /* s_closing  */
accept_init:
T0_init:
	if
	:: ((s_closing)) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_06 */
never {    /* s_time_wait
 */
accept_init:
T0_init:
	if
	:: ((s_time_wait)) -> goto accept_all
	fi;
accept_all:
	skip
}

/* leaving the exit state */

/* LTL_07 */
never {    /* c_exit && <>!c_exit
 */
T0_init:
	if
	:: ((c_exit)) -> goto T0_S3
	fi;
T0_S3:
	if
	:: (! ((c_exit))) -> goto accept_all
	:: (1) -> goto T0_S3
	fi;
accept_all:
	skip
}

/* LTL_08 */
never {    /* s_exit && <>!s_exit
 */
T0_init:
	if
	:: ((s_exit)) -> goto T0_S3
	fi;
T0_S3:
	if
	:: (! ((s_exit))) -> goto accept_all
	:: (1) -> goto T0_S3
	fi;
accept_all:
	skip
}

/* valid transitions */

/* LTL_09 */
never {    /* c_closed && !(c_closed U (c_syn_sent || c_exit))
 */
accept_init:
T0_init:
	if
	:: (! ((c_exit)) && ! ((c_syn_sent)) && (c_closed)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_exit)) && ! ((c_syn_sent))) -> goto accept_S3
	:: (! ((c_closed)) && ! ((c_exit)) && ! ((c_syn_sent))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_10 */
never {    /* c_listen && !(c_listen U (c_closed || c_syn_sent))
 */
accept_init:
T0_init:
	if
	:: (! ((c_closed)) && ! ((c_syn_sent)) && (c_listen)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_closed)) && ! ((c_syn_sent))) -> goto accept_S3
	:: (! ((c_closed)) && ! ((c_listen)) && ! ((c_syn_sent))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_11 */
never {    /* c_syn_sent && !(c_syn_sent U (c_established || c_syn_received))
 */
accept_init:
T0_init:
	if
	:: (! ((c_established)) && ! ((c_syn_received)) && (c_syn_sent)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_established)) && ! ((c_syn_received))) -> goto accept_S3
	:: (! ((c_established)) && ! ((c_syn_received)) && ! ((c_syn_sent))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_12 */
never {    /* c_established && !(c_established U (c_fin_wait_1))
 */
accept_init:
T0_init:
	if
	:: (! ((c_fin_wait_1)) && (c_established)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_fin_wait_1))) -> goto accept_S3
	:: (! ((c_established)) && ! ((c_fin_wait_1))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_13 */
never {    /* c_fin_wait_1 && !(c_fin_wait_1 U (c_fin_wait_2 || c_closing || c_time_wait))
 */
accept_init:
T0_init:
	if
	:: (! ((c_closing)) && ! ((c_fin_wait_2)) && ! ((c_time_wait)) && (c_fin_wait_1)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_closing)) && ! ((c_fin_wait_2)) && ! ((c_time_wait))) -> goto accept_S3
	:: (! ((c_closing)) && ! ((c_fin_wait_1)) && ! ((c_fin_wait_2)) && ! ((c_time_wait))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_14 */
never {    /* c_fin_wait_2 && !(c_fin_wait_2 U (c_time_wait))
 */
accept_init:
T0_init:
	if
	:: (! ((c_time_wait)) && (c_fin_wait_2)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_time_wait))) -> goto accept_S3
	:: (! ((c_fin_wait_2)) && ! ((c_time_wait))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_15 */
never {    /* c_closing && !(c_closing U c_time_wait)
 */
accept_init:
T0_init:
	if
	:: (! ((c_time_wait)) && (c_closing)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_time_wait))) -> goto accept_S3
	:: (! ((c_closing)) && ! ((c_time_wait))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_16 */
never {    /* c_time_wait && !(c_time_wait U c_closed)
 */
accept_init:
T0_init:
	if
	:: (! ((c_closed)) && (c_time_wait)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((c_closed))) -> goto accept_S3
	:: (! ((c_closed)) && ! ((c_time_wait))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_17 */
never {    /* s_closed && !(s_closed U (s_listen || s_syn_sent || s_exit))
 */
accept_init:
T0_init:
	if
	:: (! ((s_exit)) && ! ((s_listen)) && ! ((s_syn_sent)) && (s_closed)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((s_exit)) && ! ((s_listen)) && ! ((s_syn_sent))) -> goto accept_S3
	:: (! ((s_closed)) && ! ((s_exit)) && ! ((s_listen)) && ! ((s_syn_sent))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_18 */
never {    /* s_listen && !(s_listen U s_syn_received)
 */
accept_init:
T0_init:
	if
	:: (! ((s_syn_received)) && (s_listen)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((s_syn_received))) -> goto accept_S3
	:: (! ((s_listen)) && ! ((s_syn_received))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_19 */
never {    /* s_syn_sent && !(s_syn_sent U s_established)
 */
accept_init:
T0_init:
	if
	:: (! ((s_established)) && (s_syn_sent)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((s_established))) -> goto accept_S3
	:: (! ((s_established)) && ! ((s_syn_sent))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_20 */
never {    /* s_syn_received && !(s_syn_received U s_established)
 */
accept_init:
T0_init:
	if
	:: (! ((s_established)) && (s_syn_received)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((s_established))) -> goto accept_S3
	:: (! ((s_established)) && ! ((s_syn_received))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_21 */
never {    /* s_established && !(s_established U s_close_wait)
 */
accept_init:
T0_init:
	if
	:: (! ((s_close_wait)) && (s_established)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((s_close_wait))) -> goto accept_S3
	:: (! ((s_close_wait)) && ! ((s_established))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_22 */
never {    /* s_close_wait && !(s_close_wait U s_last_ack)
 */
accept_init:
T0_init:
	if
	:: (! ((s_last_ack)) && (s_close_wait)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((s_last_ack))) -> goto accept_S3
	:: (! ((s_close_wait)) && ! ((s_last_ack))) -> goto accept_all
	fi;
accept_all:
	skip
}

/* LTL_23 */
never {    /* s_last_ack && !(s_last_ack U s_closed)
 */
accept_init:
T0_init:
	if
	:: (! ((s_closed)) && (s_last_ack)) -> goto accept_S3
	fi;
accept_S3:
T0_S3:
	if
	:: (! ((s_closed))) -> goto accept_S3
	:: (! ((s_closed)) && ! ((s_last_ack))) -> goto accept_all
	fi;
accept_all:
	skip
}
