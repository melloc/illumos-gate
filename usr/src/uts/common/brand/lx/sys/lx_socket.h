/*
 * CDDL HEADER START
 *
 * The contents of this file are subject to the terms of the
 * Common Development and Distribution License (the "License").
 * You may not use this file except in compliance with the License.
 *
 * You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
 * or http://www.opensolaris.org/os/licensing.
 * See the License for the specific language governing permissions
 * and limitations under the License.
 *
 * When distributing Covered Code, include this CDDL HEADER in each
 * file and include the License file at usr/src/OPENSOLARIS.LICENSE.
 * If applicable, add the following below this CDDL HEADER, with the
 * fields enclosed by brackets "[]" replaced with your own identifying
 * information: Portions Copyright [yyyy] [name of copyright owner]
 *
 * CDDL HEADER END
 */
/*
 * Copyright 2009 Sun Microsystems, Inc.  All rights reserved.
 * Use is subject to license terms.
 * Copyright 2016 Joyent, Inc.
 * Copyright 2019 OmniOS Community Edition (OmniOSce) Association.
 */

#ifndef _SYS_LX_SOCKET_H
#define	_SYS_LX_SOCKET_H

#ifdef	__cplusplus
extern "C" {
#endif

/*
 * Linux address family definitions
 * Some of these are not supported
 */
#define	LX_AF_UNSPEC		0  /* Unspecified */
#define	LX_AF_UNIX		1  /* local file/pipe name */
#define	LX_AF_INET		2  /* IP protocol family */
#define	LX_AF_AX25		3  /* Amateur Radio AX.25 */
#define	LX_AF_IPX		4  /* Novell Internet Protocol */
#define	LX_AF_APPLETALK		5  /* Appletalk */
#define	LX_AF_NETROM		6  /* Amateur radio */
#define	LX_AF_BRIDGE		7  /* Multiprotocol bridge */
#define	LX_AF_ATMPVC		8  /* ATM PVCs */
#define	LX_AF_X25		9  /* X.25 */
#define	LX_AF_INET6		10 /* IPV 6 */
#define	LX_AF_ROSE		11 /* Amateur Radio X.25 */
#define	LX_AF_DECNET		12 /* DECnet */
#define	LX_AF_NETBEUI		13 /* 802.2LLC */
#define	LX_AF_SECURITY		14 /* Security callback */
#define	LX_AF_KEY		15 /* key management */
#define	LX_AF_ROUTE		16 /* Alias to emulate 4.4BSD */
#define	LX_AF_NETLINK		LX_AF_ROUTE
#define	LX_AF_PACKET		17 /* Packet family */
#define	LX_AF_ASH		18 /* Ash ? */
#define	LX_AF_ECONET		19 /* Acorn Econet */
#define	LX_AF_ATMSVC		20 /* ATM SVCs */
#define	LX_AF_SNA		22 /* Linux SNA */
#define	LX_AF_IRDA		23 /* IRDA sockets */
#define	LX_AF_PPPOX		24 /* PPPoX sockets */
#define	LX_AF_WANPIPE		25 /* Wanpipe API sockets */
#define	LX_AF_LLC		26
/* gap in Linux defines for 27 and 28 */
#define	LX_AF_CAN		29
#define	LX_AF_TIPC		30
#define	LX_AF_BLUETOOTH		31 /* Bluetooth sockets */
#define	LX_AF_IUCV		32
#define	LX_AF_RXRPC		33

/* limit of AF mappings */
#define	LX_AF_MAX		LX_AF_RXRPC

#define	AF_NOTSUPPORTED		-1
#define	AF_INVAL		-2

/*
 * Options for use with [gs]etsockopt at the SOL_SOCKET level.
 */
#define	LX_SOL_SOCKET				1

#define	LX_SCM_RIGHTS				1
#define	LX_SCM_CRED				2

#define	LX_SO_DEBUG				1
#define	LX_SO_REUSEADDR				2
#define	LX_SO_TYPE				3
#define	LX_SO_ERROR				4
#define	LX_SO_DONTROUTE				5
#define	LX_SO_BROADCAST				6
#define	LX_SO_SNDBUF				7
#define	LX_SO_RCVBUF				8
#define	LX_SO_KEEPALIVE				9
#define	LX_SO_OOBINLINE				10
#define	LX_SO_NO_CHECK				11
#define	LX_SO_PRIORITY				12
#define	LX_SO_LINGER				13
#define	LX_SO_BSDCOMPAT				14
#define	LX_SO_REUSEPORT				15
/*
 * For Linux see unix(7) man page SO_PASSCRED description. For Illumos see
 * socket.h(3HEAD) man page SO_RECVUCRED description.
 */
#define	LX_SO_PASSCRED				16
#define	LX_SO_PEERCRED				17
#define	LX_SO_RCVLOWAT				18
#define	LX_SO_SNDLOWAT				19
#define	LX_SO_RCVTIMEO				20
#define	LX_SO_SNDTIMEO				21
/* Security levels - as per NRL IPv6 - don't actually do anything */
#define	LX_SO_SECURITY_AUTHENTICATION		22
#define	LX_SO_SECURITY_ENCRYPTION_TRANSPORT	23
#define	LX_SO_SECURITY_ENCRYPTION_NETWORK	24
#define	LX_SO_BINDTODEVICE			25
/* Socket filtering */
#define	LX_SO_ATTACH_FILTER			26
#define	LX_SO_DETACH_FILTER			27
#define	LX_SO_PEERNAME				28
#define	LX_SO_TIMESTAMP				29
#define	LX_SCM_TIMESTAMP			LX_SO_TIMESTAMP
#define	LX_SO_ACCEPTCONN			30

#define	LX_SO_PEERSEC				31
#define	LX_SO_SNDBUFFORCE			32
#define	LX_SO_RCVBUFFORCE			33
#define	LX_SO_PASSSEC				34
#define	LX_SO_TIMESTAMPNS			35
#define	LX_SCM_TIMESTAMPNS			LX_SO_TIMESTAMPNS
#define	LX_SO_MARK				36
#define	LX_SO_TIMESTAMPING			37
#define	LX_SCM_TIMESTAMPING			LX_SO_TIMESTAMPING
#define	LX_SO_PROTOCOL				38
#define	LX_SO_DOMAIN				39
#define	LX_SO_RXQ_OVFL				40
#define	LX_SO_WIFI_STATUS			41
#define	LX_SCM_WIFI_STATUS			LX_SO_WIFI_STATUS
#define	LX_SO_PEEK_OFF				42
#define	LX_SO_NOFCS				43
#define	LX_SO_LOCK_FILTER			44
#define	LX_SO_SELECT_ERR_QUEUE			45
#define	LX_SO_BUSY_POLL				46
#define	LX_SO_MAX_PACING_RATE			47
#define	LX_SO_BPF_EXTENSIONS			48

/*
 * Options for use with [gs]etsockopt at the RAW level.
 * IPPROTO_RAW
 */
#define	LX_ICMP_FILTER				1

/*
 * Options for use with [gs]etsockopt at the PACKET level.
 * SOL_PACKET
 */
#define	LX_SOL_PACKET				263

#define	LX_PACKET_ADD_MEMBERSHIP		1
#define	LX_PACKET_DROP_MEMBERSHIP		2
#define	LX_PACKET_RECV_OUTPUT			3
#define	LX_PACKET_RX_RING			5
#define	LX_PACKET_STATISTICS			6

/*
 * Options for use with [gs]etsockopt at the NETLINK level.
 * SOL_NETLINK
 */
#define	LX_SOL_NETLINK				270

/*
 * Linux socket type definitions
 */
#define	LX_SOCK_STREAM		1	/* Connection-based byte streams */
#define	LX_SOCK_DGRAM		2	/* Connectionless, datagram */
#define	LX_SOCK_RAW		3	/* Raw protocol interface */
#define	LX_SOCK_RDM		4	/* Reliably-delivered message */
#define	LX_SOCK_SEQPACKET	5	/* Sequenced packet stream */
#define	LX_SOCK_PACKET		10	/* Linux specific */
#define	LX_SOCK_MAX		11

/*
 * The Linux socket type can be or-ed with other flags (e.g. SOCK_CLOEXEC).
 */
#define	LX_SOCK_TYPE_MASK	0xf

/*
 * Linux flags for socket, socketpair and accept4. These are or-ed into the
 * socket type value. In the Linux net.h header these come from fcntl.h (note
 * that they are in octal in the Linux header).
 */
#define	LX_SOCK_CLOEXEC		0x80000
#define	LX_SOCK_NONBLOCK	0x800

#define	SOCK_NOTSUPPORTED	-1
#define	SOCK_INVAL		-2

/*
 * PF_PACKET protocol definitions.
 */
#define	LX_ETH_P_802_3	0x0001
#define	LX_ETH_P_ALL	0x0003
#define	LX_ETH_P_802_2	0x0004
#define	LX_ETH_P_IP	0x0800
#define	LX_ETH_P_ARP	0x0806
#define	LX_ETH_P_IPV6	0x86DD

/*
 * IP Protocol levels. Some of these match the Illumos IPPROTO_* values.
 */
#define	LX_IPPROTO_IP		0
#define	LX_IPPROTO_ICMP		1
#define	LX_IPPROTO_IGMP		2
#define	LX_IPPROTO_TCP		6
#define	LX_IPPROTO_UDP		17
#define	LX_IPPROTO_IPV6		41
#define	LX_IPPROTO_ICMPV6	58
#define	LX_IPPROTO_RAW		255

/*
 * Options for use with [gs]etsockopt at the IP level.
 * IPPROTO_IP
 */
#define	LX_IP_TOS		1
#define	LX_IP_TTL		2
#define	LX_IP_HDRINCL		3
#define	LX_IP_OPTIONS		4
#define	LX_IP_ROUTER_ALERT	5
#define	LX_IP_RECVOPTS		6
#define	LX_IP_RETOPTS		7
#define	LX_IP_PKTINFO		8
#define	LX_IP_PKTOPTIONS	9
#define	LX_IP_MTU_DISCOVER	10
#define	LX_IP_RECVERR		11
#define	LX_IP_RECVTTL		12
#define	LX_IP_RECVTOS		13
#define	LX_IP_MTU		14
#define	LX_IP_FREEBIND		15
#define	LX_IP_IPSEC_POLICY	16
#define	LX_IP_XFRM_POLICY	17
#define	LX_IP_PASSSEC		18
#define	LX_IP_TRANSPARENT	19
#define	LX_IP_ORIGDSTADDR	20
#define	LX_IP_MINTTL		21
#define	LX_IP_NODEFRAG		22
/* Linux apparently leaves a gap here */
#define	LX_IP_MULTICAST_IF	32
#define	LX_IP_MULTICAST_TTL	33
#define	LX_IP_MULTICAST_LOOP	34
#define	LX_IP_ADD_MEMBERSHIP	35
#define	LX_IP_DROP_MEMBERSHIP	36
#define	LX_IP_UNBLOCK_SOURC	37
#define	LX_IP_BLOCK_SOURCE	38
#define	LX_IP_ADD_SOURCE_MEMBERSHIP 39
#define	LX_IP_DROP_SOURCE_MEMBERSHIP 40
#define	LX_IP_MSFILTER		41
#define	LX_MCAST_JOIN_GROUP	42
#define	LX_MCAST_BLOCK_SOURCE	43
#define	LX_MCAST_UNBLOCK_SOURCE	44
#define	LX_MCAST_LEAVE_GROUP	45
#define	LX_MCAST_JOIN_SOURCE_GROUP 46
#define	LX_MCAST_LEAVE_SOURCE_GROUP 47
#define	LX_MCAST_MSFILTER	48
#define	LX_IP_MULTICAST_ALL	49
#define	LX_IP_UNICAST_IF	50

/*
 * LX_IP_MTU_DISCOVER values
 */
#define	LX_IP_PMTUDISC_DONT		0
#define	LX_IP_PMTUDISC_WANT		1
#define	LX_IP_PMTUDISC_DO		2
#define	LX_IP_PMTUDISC_PROBE		3
#define	LX_IP_PMTUDISC_INTERFACE	4
#define	LX_IP_PMTUDISC_OMIT		5

/*
 * Options for use with [gs]etsockopt at the IP level.
 * IPPROTO_IPV6
 */

#define	LX_IPV6_ADDRFORM	1
#define	LX_IPV6_2292PKTINFO	2
#define	LX_IPV6_2292HOPOPTS	3
#define	LX_IPV6_2292DSTOPTS	4
#define	LX_IPV6_2292RTHDR	5
#define	LX_IPV6_2292PKTOPTIONS	6
#define	LX_IPV6_CHECKSUM	7
#define	LX_IPV6_2292HOPLIMIT	8
#define	LX_IPV6_NEXTHOP		9
#define	LX_IPV6_AUTHHDR		10
#define	LX_IPV6_UNICAST_HOPS	16
#define	LX_IPV6_MULTICAST_IF	17
#define	LX_IPV6_MULTICAST_HOPS	18
#define	LX_IPV6_MULTICAST_LOOP	19
#define	LX_IPV6_JOIN_GROUP	20
#define	LX_IPV6_LEAVE_GROUP	21
#define	LX_IPV6_ROUTER_ALERT	22
#define	LX_IPV6_MTU_DISCOVER	23
#define	LX_IPV6_MTU		24
#define	LX_IPV6_RECVERR		25
#define	LX_IPV6_V6ONLY		26
#define	LX_IPV6_JOIN_ANYCAST	27
#define	LX_IPV6_LEAVE_ANYCAST	28
#define	LX_IPV6_IPSEC_POLICY	34
#define	LX_IPV6_XFRM_POLICY	35

#define	LX_IPV6_RECVPKTINFO	49
#define	LX_IPV6_PKTINFO		50
#define	LX_IPV6_RECVHOPLIMIT	51
#define	LX_IPV6_HOPLIMIT	52
#define	LX_IPV6_RECVHOPOPTS	53
#define	LX_IPV6_HOPOPTS		54
#define	LX_IPV6_RTHDRDSTOPTS	55
#define	LX_IPV6_RECVRTHDR	56
#define	LX_IPV6_RTHDR		57
#define	LX_IPV6_RECVDSTOPTS	58
#define	LX_IPV6_DSTOPTS		59
#define	LX_IPV6_RECVTCLASS	66
#define	LX_IPV6_TCLASS		67

/*
 * Options for use with [gs]etsockopt at the IP level.
 * IPPROTO_ICMPV6
 */

#define	LX_ICMP6_FILTER		1

/*
 * Options for use with [gs]etsockopt at the TCP level.
 * IPPROTO_TCP
 */
#define	LX_TCP_NODELAY		1  /* Don't delay send to coalesce packets  */
#define	LX_TCP_MAXSEG		2  /* Set maximum segment size  */
#define	LX_TCP_CORK		3  /* Control sending of partial frames  */
#define	LX_TCP_KEEPIDLE		4  /* Start keeplives after this period */
#define	LX_TCP_KEEPINTVL	5  /* Interval between keepalives */
#define	LX_TCP_KEEPCNT		6  /* Number of keepalives before death */
#define	LX_TCP_SYNCNT		7  /* Number of SYN retransmits */
#define	LX_TCP_LINGER2		8  /* Life time of orphaned FIN-WAIT-2 state */
#define	LX_TCP_DEFER_ACCEPT	9  /* Wake up listener only when data arrive */
#define	LX_TCP_WINDOW_CLAMP	10 /* Bound advertised window */
#define	LX_TCP_INFO		11 /* Information about this connection. */
#define	LX_TCP_QUICKACK		12 /* Bock/reenable quick ACKs.  */
#define	LX_TCP_CONGESTION	13 /* Congestion control algorithm */
#define	LX_TCP_MD5SIG		14 /* TCP MD5 Signature (RFC2385) */
#define	LX_TCP_THIN_LINEAR_TIMEOUTS 16 /* Use linear timeouts on thin streams */
#define	LX_TCP_THIN_DUPACK	17 /* Fast retrans. after 1 dupack */
#define	LX_TCP_USER_TIMEOUT	18 /* How long for loss retry before timeout */
#define	LX_TCP_REPAIR		19 /* TCP socket under repair */
#define	LX_TCP_REPAIR_QUEUE	20
#define	LX_TCP_QUEUE_SEQ	21
#define	LX_TCP_REPAIR_OPTIONS	22
#define	LX_TCP_FASTOPEN		23 /* Enable FastOpen on listeners */
#define	LX_TCP_TIMESTAMP	24
#define	LX_TCP_NOTSENT_LOWAT	25 /* limit number of unsent bytes */

/*
 * Options for use with [gs]etsockopt at the IGMP level.
 * IPPROTO_IGMP
 */
#define	LX_IGMP_MINLEN				8
#define	LX_IGMP_MAX_HOST_REPORT_DELAY		10
#define	LX_IGMP_HOST_MEMBERSHIP_QUERY		0x11
#define	LX_IGMP_HOST_MEMBERSHIP_REPORT		0x12
#define	LX_IGMP_DVMRP				0x13
#define	LX_IGMP_PIM				0x14
#define	LX_IGMP_TRACE				0x15
#define	LX_IGMP_HOST_NEW_MEMBERSHIP_REPORT	0x16
#define	LX_IGMP_HOST_LEAVE_MESSAGE		0x17
#define	LX_IGMP_MTRACE_RESP			0x1e
#define	LX_IGMP_MTRACE				0x1f

/*
 * Linux socket flags for use with recv(2)/send(2)/recvmsg(2)/sendmsg(2)
 */
#define	LX_MSG_OOB		0x1
#define	LX_MSG_PEEK		0x2
#define	LX_MSG_DONTROUTE	0x4
#define	LX_MSG_CTRUNC		0x8
#define	LX_MSG_PROXY		0x10
#define	LX_MSG_TRUNC		0x20
#define	LX_MSG_DONTWAIT		0x40
#define	LX_MSG_EOR		0x80
#define	LX_MSG_WAITALL		0x100
#define	LX_MSG_FIN		0x200
#define	LX_MSG_SYN		0x400
#define	LX_MSG_CONFIRM		0x800
#define	LX_MSG_RST		0x1000
#define	LX_MSG_ERRQUEUE		0x2000
#define	LX_MSG_NOSIGNAL		0x4000
#define	LX_MSG_MORE		0x8000
#define	LX_MSG_WAITFORONE	0x10000
#define	LX_MSG_FASTOPEN		0x20000000
#define	LX_MSG_CMSG_CLOEXEC	0x40000000

typedef struct lx_msghdr {
	void		*msg_name;	/* optional address */
	socklen_t	msg_namelen;	/* size of address */
	struct iovec	*msg_iov;	/* scatter/gather array */
	size_t		msg_iovlen;	/* # elements in msg_iov */
	void		*msg_control;	/* ancillary data */
	size_t		msg_controllen;	/* ancillary data buffer len */
	int		msg_flags;	/* flags on received message */
} lx_msghdr_t;

typedef struct lx_mmsghdr {
	lx_msghdr_t	msg_hdr;	/* message header */
	unsigned int	msg_len;	/* no. of bytes transmitted */
} lx_mmsghdr_t;

#if defined(_LP64)

typedef struct lx_msghdr32 {
	caddr32_t	msg_name;	/* optional address */
	uint32_t	msg_namelen;	/* size of address */
	caddr32_t	msg_iov;	/* scatter/gather array */
	int32_t		msg_iovlen;	/* # elements in msg_iov */
	caddr32_t	msg_control;	/* ancillary data */
	uint32_t	msg_controllen;	/* ancillary data buffer len */
	int32_t		msg_flags;	/* flags on received message */
} lx_msghdr32_t;

typedef struct lx_mmsghdr32 {
	lx_msghdr32_t	msg_hdr;	/* message header */
	unsigned int	msg_len;	/* no. of bytes transmitted */
} lx_mmsghdr32_t;

#endif

typedef struct lx_sockaddr_in6 {
	sa_family_t	sin6_family;
	in_port_t	sin6_port;
	uint32_t	sin6_flowinfo;
	struct in6_addr	sin6_addr;
	uint32_t	sin6_scope_id;  /* Depends on scope of sin6_addr */
	/* one 32-bit field shorter than illumos */
} lx_sockaddr_in6_t;

typedef struct lx_tcp_info {
	/* Current state in TCP state machine */
	uint8_t		tcpi_state;
	/* Congestion avoidance state */
	uint8_t		tcpi_ca_state;
	/* Number of unrecovered RTO timeouts */
	uint8_t		tcpi_retransmits;
	/* Unanswered 0 window probes */
	uint8_t		tcpi_probes;
	/* Current exponential backoff for RTO */
	uint8_t		tcpi_backoff;
	/* Enabled TCP options */
	uint8_t		tcpi_options;
#define	LX_TCPI_OPT_TIMESTAMPS	0x01	/* Negotiated TCP Timestamps */
#define	LX_TCPI_OPT_SACK	0x02	/* Negotiated SACK */
#define	LX_TCPI_OPT_WSCALE	0x04	/* Negotiated Window Scaling */
#define	LX_TCPI_OPT_ECN		0x08	/* Negotiated ECN */
#define	LX_TCPI_OPT_ECN_SEEN	0x10	/* Received at least 1 packet w/ ECT */
#define	LX_TCPI_OPT_SYN_DATA	0x20	/* Sent or received SYN-ACK for SYN */

	uint8_t
		tcpi_snd_wscale : 4,	/* Send window scale shift */
		tcpi_rcv_wscale : 4;	/* Receive window scale shift */

	/* Whether the application is sending less than the send window */
	uint8_t		tcpi_delivery_rate_app_limited : 1;

	/* Retransmission timeout (usecs) */
	uint32_t	tcpi_rto;
	/* Predicted soft clock tick for delivering delayed ACK */
	uint32_t	tcpi_ato;
	/* Maximum Segment Size, sent (RFC 4898 tcpEStatsStackMSSSent) */
	uint32_t	tcpi_snd_mss;
	/* Maximum Segment Size, received (RFC 4898 tcpEStatsStackMSSRcvd) */
	uint32_t	tcpi_rcv_mss;

	/* Sent but unacknowledged bytes */
	uint32_t	tcpi_unacked;
	/* With SACK, ; without, # of recvd dups */
	uint32_t	tcpi_sacked;
	/* Estimated # of packets lost */
	uint32_t	tcpi_lost;
	/* Total # of rexmitted segments */
	uint32_t	tcpi_retrans;
	/* # of packets to highest SACKed sequence (deprecated on Linux)*/
	uint32_t	tcpi_fackets;

	/* Time (msecs) since last sent data */
	uint32_t	tcpi_last_data_sent;
	/* Time (msecs) since last sent ACK (not filled in on Linux) */
	uint32_t	tcpi_last_ack_sent;
	/* Time (msecs) since last recv data */
	uint32_t	tcpi_last_data_recv;
	/* Time (msecs) since last recv ACK */
	uint32_t	tcpi_last_ack_recv;

	/* Last PMTU seen by socket */
	uint32_t	tcpi_pmtu;
	/* Slow start threshold (recv) */
	uint32_t	tcpi_rcv_ssthresh;
	/* Smoothed RTT (usecs) */
	uint32_t	tcpi_rtt;
	/* RTT variance (usecs) */
	uint32_t	tcpi_rttvar;
	/* Slow start threshold (send) */
	uint32_t	tcpi_snd_ssthresh;
	/* Send congestion window */
	uint32_t	tcpi_snd_cwnd;
	/* Advertised MSS */
	uint32_t	tcpi_advmss;
	/* ? */
	uint32_t	tcpi_reordering;

	/* ? */
	uint32_t	tcpi_rcv_rtt;
	/* Advertised recv window */
	uint32_t	tcpi_rcv_space;

	/* Total # of rexmitted segments for connection */
	uint32_t	tcpi_total_retrans;

	/* ? */
	uint64_t	tcpi_pacing_rate;
	/* ? */
	uint64_t	tcpi_max_pacing_rate;
	/* RFC 4898 tcpEStatsAppHCThruOctetsAcked */
	uint64_t	tcpi_bytes_acked;
	/* RFC 4898 tcpEStatsAppHCThruOctetsReceived */
	uint64_t	tcpi_bytes_received;
	/* RFC 4898 tcpEStatsPerfSegsOut */
	uint32_t	tcpi_segs_out;
	/* RFC 4898 tcpEStatsPerfSegsIn */
	uint32_t	tcpi_segs_in;
	/* Current # of unsent bytes */
	uint32_t	tcpi_notsent_bytes;
	/* Minimum observed RTT */
	uint32_t	tcpi_min_rtt;
	/* RFC 4898 tcpEStatsDataSegsIn */
	uint32_t	tcpi_data_segs_in;
	/* RFC 4898 tcpEStatsDataSegsOut */
	uint32_t	tcpi_data_segs_out;
	/* ? */
	uint64_t	tcpi_delivery_rate;
	/* Time (usecs) busy sending data */
	uint64_t	tcpi_busy_time;
	/* Time (usecs) limited by received window */
	uint64_t	tcpi_rwnd_limited;
	/* Time (usecs) limited by send buffer */
	uint64_t	tcpi_sndbuf_limited;

	/* Total # of data packets delivered to peer, including rexmits */
	uint32_t	tcpi_delivered;
	/* Same as the above field, but only counts ECE-marked packets */
	uint32_t	tcpi_delivered_ce;

	/* RFC 4898 tcpEStatsPerfHCDataOctetsOut */
	uint64_t	tcpi_bytes_sent;
	/* Total # of bytes rexmitted (RFC 4898 tcpEStatsPerfOctetsRetrans) */
	uint64_t	tcpi_bytes_retrans;
	/* RFC 4898 tcpEStatsStackDSACKDups */
	uint32_t	tcpi_dsack_dups;
	/* # of reordering events seen */
	uint32_t	tcpi_reord_seen;
} lx_tcp_info_t;

#ifdef	__cplusplus
}
#endif

#endif	/* _SYS_LX_SOCKET_H */
