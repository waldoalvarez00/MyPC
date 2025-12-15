; z80dasm 1.1.6
; command line: z80dasm -a -t -g 0x8000 -o /tmp/mrdo_disasm.asm roms/mrdo-usa-europe.col

	org	08000h

	xor d			;8000	aa 	. 
	ld d,l			;8001	55 	U 
	jp (hl)			;8002	e9 	. 
	ld (hl),b			;8003	70 	p 
	nop			;8004	00 	. 
	ld (hl),b			;8005	70 	p 
	rst 28h			;8006	ef 	. 
	ld (hl),d			;8007	72 	r 
	add a,(hl)			;8008	86 	. 
	ld (hl),b			;8009	70 	p 
	dec a			;800a	3d 	= 
	add a,e			;800b	83 	. 
	ret			;800c	c9 	. 
	nop			;800d	00 	. 
	nop			;800e	00 	. 
	ret			;800f	c9 	. 
	nop			;8010	00 	. 
	nop			;8011	00 	. 
	ret			;8012	c9 	. 
	nop			;8013	00 	. 
	nop			;8014	00 	. 
	ret			;8015	c9 	. 
	nop			;8016	00 	. 
	nop			;8017	00 	. 
	ret			;8018	c9 	. 
	nop			;8019	00 	. 
	nop			;801a	00 	. 
	ret			;801b	c9 	. 
	nop			;801c	00 	. 
	nop			;801d	00 	. 
	reti		;801e	ed 4d 	. M 
	nop			;8020	00 	. 
	jp 08047h		;8021	c3 47 80 	. G . 
	ld c,l			;8024	4d 	M 
	ld d,d			;8025	52 	R 
	ld l,020h		;8026	2e 20 	.   
	ld b,h			;8028	44 	D 
	ld c,a			;8029	4f 	O 
	ld hl,01f1eh		;802a	21 1e 1f 	! . . 
	cpl			;802d	2f 	/ 
	ld d,b			;802e	50 	P 
	ld d,d			;802f	52 	R 
	ld b,l			;8030	45 	E 
	ld d,e			;8031	53 	S 
	ld b,l			;8032	45 	E 
	ld c,(hl)			;8033	4e 	N 
	ld d,h			;8034	54 	T 
	ld d,e			;8035	53 	S 
	jr nz,$+87		;8036	20 55 	  U 
	ld c,(hl)			;8038	4e 	N 
	ld c,c			;8039	49 	I 
	ld d,(hl)			;803a	56 	V 
	ld b,l			;803b	45 	E 
	ld d,d			;803c	52 	R 
	ld d,e			;803d	53 	S 
	ld b,c			;803e	41 	A 
	ld c,h			;803f	4c 	L 
	daa			;8040	27 	' 
	ld d,e			;8041	53 	S 
	cpl			;8042	2f 	/ 
	ld sp,03839h		;8043	31 39 38 	1 9 8 
	inc sp			;8046	33 	3 
	push af			;8047	f5 	. 
	push bc			;8048	c5 	. 
	push de			;8049	d5 	. 
	push hl			;804a	e5 	. 
	ex af,af'			;804b	08 	. 
	exx			;804c	d9 	. 
	push af			;804d	f5 	. 
	push bc			;804e	c5 	. 
	push de			;804f	d5 	. 
	push hl			;8050	e5 	. 
	push ix		;8051	dd e5 	. . 
	push iy		;8053	fd e5 	. . 
	ld bc,001c2h		;8055	01 c2 01 	. . . 
	call 01fd9h		;8058	cd d9 1f 	. . . 
	call 01fdch		;805b	cd dc 1f 	. . . 
	ld hl,072efh		;805e	21 ef 72 	! . r 
	ld de,07307h		;8061	11 07 73 	. . s 
	ld bc,00018h		;8064	01 18 00 	. . . 
	ldir		;8067	ed b0 	. . 
	ld hl,0726eh		;8069	21 6e 72 	! n r 
	bit 5,(hl)		;806c	cb 6e 	. n 
	jr z,$+16		;806e	28 0e 	( . 
	bit 4,(hl)		;8070	cb 66 	. f 
	jr z,$+45		;8072	28 2b 	( + 
	ld a,014h		;8074	3e 14 	> . 
	call 01fc4h		;8076	cd c4 1f 	. . . 
	call 08107h		;8079	cd 07 81 	. . . 
	jr $+35		;807c	18 21 	. ! 
	ld a,(0726eh)		;807e	3a 6e 72 	: n r 
	bit 3,a		;8081	cb 5f 	. _ 
	jr nz,$+10		;8083	20 08 	  . 
	ld a,014h		;8085	3e 14 	> . 
	call 01fc4h		;8087	cd c4 1f 	. . . 
	call 08107h		;808a	cd 07 81 	. . . 
	call 080d1h		;808d	cd d1 80 	. . . 
	call 08229h		;8090	cd 29 82 	. ) . 
	call 08251h		;8093	cd 51 82 	. Q . 
	call 08269h		;8096	cd 69 82 	. i . 
	call 082deh		;8099	cd de 82 	. . . 
	call 01fd3h		;809c	cd d3 1f 	. . . 
	call 01febh		;809f	cd eb 1f 	. . . 
	call 0c952h		;80a2	cd 52 c9 	. R . 
	ld hl,07307h		;80a5	21 07 73 	! . s 
	ld de,072efh		;80a8	11 ef 72 	. . r 
	ld bc,00018h		;80ab	01 18 00 	. . . 
	ldir		;80ae	ed b0 	. . 
	ld hl,0726eh		;80b0	21 6e 72 	! n r 
	bit 7,(hl)		;80b3	cb 7e 	. ~ 
	jr z,$+6		;80b5	28 04 	( . 
	res 7,(hl)		;80b7	cb be 	. . 
	jr $+8		;80b9	18 06 	. . 
	ld bc,001e2h		;80bb	01 e2 01 	. . . 
	call 01fd9h		;80be	cd d9 1f 	. . . 
	pop iy		;80c1	fd e1 	. . 
	pop ix		;80c3	dd e1 	. . 
	pop hl			;80c5	e1 	. 
	pop de			;80c6	d1 	. 
	pop bc			;80c7	c1 	. 
	pop af			;80c8	f1 	. 
	exx			;80c9	d9 	. 
	ex af,af'			;80ca	08 	. 
	pop hl			;80cb	e1 	. 
	pop de			;80cc	d1 	. 
	pop bc			;80cd	c1 	. 
	pop af			;80ce	f1 	. 
	retn		;80cf	ed 45 	. E 
	ld hl,07259h		;80d1	21 59 72 	! Y r 
	ld bc,01401h		;80d4	01 01 14 	. . . 
	ld a,(hl)			;80d7	7e 	~ 
	and a			;80d8	a7 	. 
	jr z,$+38		;80d9	28 24 	( $ 
	ld e,c			;80db	59 	Y 
	push bc			;80dc	c5 	. 
	push hl			;80dd	e5 	. 
	push de			;80de	d5 	. 
	ld hl,07259h		;80df	21 59 72 	! Y r 
	ld a,e			;80e2	7b 	{ 
	call 0ac0bh		;80e3	cd 0b ac 	. . . 
	jr z,$+17		;80e6	28 0f 	( . 
	pop de			;80e8	d1 	. 
	push de			;80e9	d5 	. 
	ld hl,07259h		;80ea	21 59 72 	! Y r 
	ld a,e			;80ed	7b 	{ 
	call 0abf6h		;80ee	cd f6 ab 	. . . 
	pop de			;80f1	d1 	. 
	push de			;80f2	d5 	. 
	ld a,e			;80f3	7b 	{ 
	call 0b19ch		;80f4	cd 9c b1 	. . . 
	pop de			;80f7	d1 	. 
	inc e			;80f8	1c 	. 
	pop hl			;80f9	e1 	. 
	ld a,(hl)			;80fa	7e 	~ 
	and a			;80fb	a7 	. 
	jr nz,$-31		;80fc	20 df 	  . 
	pop bc			;80fe	c1 	. 
	ld a,c			;80ff	79 	y 
	add a,008h		;8100	c6 08 	. . 
	ld c,a			;8102	4f 	O 
	inc hl			;8103	23 	# 
	djnz $-45		;8104	10 d1 	. . 
	ret			;8106	c9 	. 
	ld hl,08215h		;8107	21 15 82 	! . . 
	ld de,072efh		;810a	11 ef 72 	. . r 
	ld bc,00014h		;810d	01 14 00 	. . . 
	ldir		;8110	ed b0 	. . 
	ld a,003h		;8112	3e 03 	> . 
	ld (072e7h),a		;8114	32 e7 72 	2 . r 
	ld a,013h		;8117	3e 13 	> . 
	ld (072e8h),a		;8119	32 e8 72 	2 . r 
	ld hl,072f2h		;811c	21 f2 72 	! . r 
	ld iy,070f5h		;811f	fd 21 f5 70 	. ! . p 
	ld b,011h		;8123	06 11 	. . 
	ld a,(hl)			;8125	7e 	~ 
	and a			;8126	a7 	. 
	jp nz,081dch		;8127	c2 dc 81 	. . . 
	ld a,(iy+000h)		;812a	fd 7e 00 	. ~ . 
	cp 010h		;812d	fe 10 	. . 
	jr nc,$+13		;812f	30 0b 	0 . 
	ld a,(072e7h)		;8131	3a e7 72 	: . r 
	ld (hl),a			;8134	77 	w 
	inc a			;8135	3c 	< 
	ld (072e7h),a		;8136	32 e7 72 	2 . r 
	jp 081dch		;8139	c3 dc 81 	. . . 
	push bc			;813c	c5 	. 
	push hl			;813d	e5 	. 
	push iy		;813e	fd e5 	. . 
	ld de,00000h		;8140	11 00 00 	. . . 
	ld c,(iy+000h)		;8143	fd 4e 00 	. N . 
	ld a,(0726dh)		;8146	3a 6d 72 	: m r 
	res 6,a		;8149	cb b7 	. . 
	ld (0726dh),a		;814b	32 6d 72 	2 m r 
	and 003h		;814e	e6 03 	. . 
	cp 001h		;8150	fe 01 	. . 
	jr c,$+79		;8152	38 4d 	8 M 
	jr nz,$+27		;8154	20 19 	  . 
	ld d,004h		;8156	16 04 	. . 
	ld a,(070edh)		;8158	3a ed 70 	: . p 
	sub c			;815b	91 	. 
	jr nc,$+4		;815c	30 02 	0 . 
	cpl			;815e	2f 	/ 
	inc a			;815f	3c 	< 
	cp 010h		;8160	fe 10 	. . 
	jr nc,$+63		;8162	30 3d 	0 = 
	ld a,(0726dh)		;8164	3a 6d 72 	: m r 
	set 6,a		;8167	cb f7 	. . 
	ld (0726dh),a		;8169	32 6d 72 	2 m r 
	dec d			;816c	15 	. 
	jr $+52		;816d	18 32 	. 2 
	ld d,008h		;816f	16 08 	. . 
	ld a,(070edh)		;8171	3a ed 70 	: . p 
	sub c			;8174	91 	. 
	jr nc,$+4		;8175	30 02 	0 . 
	cpl			;8177	2f 	/ 
	inc a			;8178	3c 	< 
	cp 010h		;8179	fe 10 	. . 
	jr nc,$+38		;817b	30 24 	0 $ 
	ld a,(0726dh)		;817d	3a 6d 72 	: m r 
	set 6,a		;8180	cb f7 	. . 
	ld (0726dh),a		;8182	32 6d 72 	2 m r 
	ld d,006h		;8185	16 06 	. . 
	jr $+26		;8187	18 18 	. . 
	dec b			;8189	05 	. 
	jr z,$+54		;818a	28 34 	( 4 
	inc hl			;818c	23 	# 
	inc iy		;818d	fd 23 	. # 
	inc iy		;818f	fd 23 	. # 
	inc iy		;8191	fd 23 	. # 
	inc iy		;8193	fd 23 	. # 
	ld a,(iy+000h)		;8195	fd 7e 00 	. ~ . 
	sub c			;8198	91 	. 
	jr nc,$+4		;8199	30 02 	0 . 
	cpl			;819b	2f 	/ 
	inc a			;819c	3c 	< 
	cp 010h		;819d	fe 10 	. . 
	jr nc,$-22		;819f	30 e8 	0 . 
	inc e			;81a1	1c 	. 
	ld a,(hl)			;81a2	7e 	~ 
	and a			;81a3	a7 	. 
	jr nz,$-27		;81a4	20 e3 	  . 
	ld a,e			;81a6	7b 	{ 
	cp d			;81a7	ba 	. 
	jr c,$+14		;81a8	38 0c 	8 . 
	jr z,$+12		;81aa	28 0a 	( . 
	ld a,(072e7h)		;81ac	3a e7 72 	: . r 
	ld (hl),a			;81af	77 	w 
	inc a			;81b0	3c 	< 
	ld (072e7h),a		;81b1	32 e7 72 	2 . r 
	jr $-43		;81b4	18 d3 	. . 
	ld a,(072e8h)		;81b6	3a e8 72 	: . r 
	ld (hl),a			;81b9	77 	w 
	dec a			;81ba	3d 	= 
	ld (072e8h),a		;81bb	32 e8 72 	2 . r 
	jr $-53		;81be	18 c9 	. . 
	ld a,e			;81c0	7b 	{ 
	cp 009h		;81c1	fe 09 	. . 
	jr nc,$+13		;81c3	30 0b 	0 . 
	cp 007h		;81c5	fe 07 	. . 
	jr c,$+17		;81c7	38 0f 	8 . 
	ld a,(0726dh)		;81c9	3a 6d 72 	: m r 
	bit 6,a		;81cc	cb 77 	. w 
	jr z,$+10		;81ce	28 08 	( . 
	ld a,(0726dh)		;81d0	3a 6d 72 	: m r 
	set 7,a		;81d3	cb ff 	. . 
	ld (0726dh),a		;81d5	32 6d 72 	2 m r 
	pop iy		;81d8	fd e1 	. . 
	pop hl			;81da	e1 	. 
	pop bc			;81db	c1 	. 
	inc hl			;81dc	23 	# 
	inc iy		;81dd	fd 23 	. # 
	inc iy		;81df	fd 23 	. # 
	inc iy		;81e1	fd 23 	. # 
	inc iy		;81e3	fd 23 	. # 
	dec b			;81e5	05 	. 
	jp nz,08125h		;81e6	c2 25 81 	. % . 
	ld hl,0726dh		;81e9	21 6d 72 	! m r 
	ld a,(hl)			;81ec	7e 	~ 
	inc a			;81ed	3c 	< 
	and 003h		;81ee	e6 03 	. . 
	cp 002h		;81f0	fe 02 	. . 
	jr c,$+9		;81f2	38 07 	8 . 
	jr nz,$+6		;81f4	20 04 	  . 
	bit 7,(hl)		;81f6	cb 7e 	. ~ 
	jr nz,$+3		;81f8	20 01 	  . 
	xor a			;81fa	af 	. 
	ld (0726dh),a		;81fb	32 6d 72 	2 m r 
	ld de,07000h		;81fe	11 00 70 	. . p 
	ld b,014h		;8201	06 14 	. . 
	ld iy,072efh		;8203	fd 21 ef 72 	. ! . r 
	xor a			;8207	af 	. 
	ld h,000h		;8208	26 00 	& . 
	ld l,(iy+000h)		;820a	fd 6e 00 	. n . 
	add hl,de			;820d	19 	. 
	ld (hl),a			;820e	77 	w 
	inc a			;820f	3c 	< 
	inc iy		;8210	fd 23 	. # 
	djnz $-10		;8212	10 f4 	. . 
	ret			;8214	c9 	. 
	nop			;8215	00 	. 
	ld bc,00002h		;8216	01 02 00 	. . . 
	nop			;8219	00 	. 
	nop			;821a	00 	. 
	nop			;821b	00 	. 
	nop			;821c	00 	. 
	nop			;821d	00 	. 
	nop			;821e	00 	. 
	nop			;821f	00 	. 
	nop			;8220	00 	. 
	nop			;8221	00 	. 
	nop			;8222	00 	. 
	nop			;8223	00 	. 
	nop			;8224	00 	. 
	nop			;8225	00 	. 
	nop			;8226	00 	. 
	nop			;8227	00 	. 
	nop			;8228	00 	. 
	ld hl,07281h		;8229	21 81 72 	! . r 
	bit 7,(hl)		;822c	cb 7e 	. ~ 
	jr z,$+34		;822e	28 20 	(   
	res 7,(hl)		;8230	cb be 	. . 
	ld d,001h		;8232	16 01 	. . 
	ld a,(07286h)		;8234	3a 86 72 	: . r 
	and a			;8237	a7 	. 
	jr z,$+9		;8238	28 07 	( . 
	add a,01bh		;823a	c6 1b 	. . 
	call 0ad01h		;823c	cd 01 ad 	. . . 
	ld d,000h		;823f	16 00 	. . 
	ld a,(07284h)		;8241	3a 84 72 	: . r 
	sub 001h		;8244	d6 01 	. . 
	ld b,a			;8246	47 	G 
	ld a,(07285h)		;8247	3a 85 72 	: . r 
	ld c,a			;824a	4f 	O 
	ld a,081h		;824b	3e 81 	> . 
	call 0b629h		;824d	cd 29 b6 	. ) . 
	ret			;8250	c9 	. 
	ld hl,0727ch		;8251	21 7c 72 	! | r 
	bit 7,(hl)		;8254	cb 7e 	. ~ 
	jr z,$+7		;8256	28 05 	( . 
	res 7,(hl)		;8258	cb be 	. . 
	xor a			;825a	af 	. 
	jr $+10		;825b	18 08 	. . 
	bit 6,(hl)		;825d	cb 76 	. v 
	jr z,$+9		;825f	28 07 	( . 
	res 6,(hl)		;8261	cb b6 	. . 
	ld a,001h		;8263	3e 01 	> . 
	call 0b5a6h		;8265	cd a6 b5 	. . . 
	ret			;8268	c9 	. 
	ld a,(072bch)		;8269	3a bc 72 	: . r 
	and a			;826c	a7 	. 
	jr z,$+61		;826d	28 3b 	( ; 
	ld hl,082d3h		;826f	21 d3 82 	! . . 
	ld de,0002bh		;8272	11 2b 00 	. + . 
	ld bc,087e8h		;8275	01 e8 87 	. . . 
	rrca			;8278	0f 	. 
	jr c,$+9		;8279	38 07 	8 . 
	inc hl			;827b	23 	# 
	inc hl			;827c	23 	# 
	inc de			;827d	13 	. 
	inc de			;827e	13 	. 
	inc bc			;827f	03 	. 
	jr $-8		;8280	18 f6 	. . 
	ld a,(072bch)		;8282	3a bc 72 	: . r 
	and (hl)			;8285	a6 	. 
	ld (072bch),a		;8286	32 bc 72 	2 . r 
	inc hl			;8289	23 	# 
	ld a,(0726eh)		;828a	3a 6e 72 	: n r 
	bit 1,a		;828d	cb 4f 	. O 
	ld a,(072b8h)		;828f	3a b8 72 	: . r 
	jr z,$+5		;8292	28 03 	( . 
	ld a,(072b9h)		;8294	3a b9 72 	: . r 
	and (hl)			;8297	a6 	. 
	ld hl,00000h		;8298	21 00 00 	! . . 
	jr z,$+5		;829b	28 03 	( . 
	ld hl,00005h		;829d	21 05 00 	! . . 
	add hl,bc			;82a0	09 	. 
	ld a,002h		;82a1	3e 02 	> . 
	ld iy,00001h		;82a3	fd 21 01 00 	. ! . . 
	call 01fbeh		;82a7	cd be 1f 	. . . 
	ld a,(072bbh)		;82aa	3a bb 72 	: . r 
	and a			;82ad	a7 	. 
	jr z,$+36		;82ae	28 22 	( " 
	ld hl,082d3h		;82b0	21 d3 82 	! . . 
	ld de,0002bh		;82b3	11 2b 00 	. + . 
	rrca			;82b6	0f 	. 
	jr c,$+8		;82b7	38 06 	8 . 
	inc hl			;82b9	23 	# 
	inc hl			;82ba	23 	# 
	inc de			;82bb	13 	. 
	inc de			;82bc	13 	. 
	jr $-7		;82bd	18 f7 	. . 
	ld a,(072bbh)		;82bf	3a bb 72 	: . r 
	and (hl)			;82c2	a6 	. 
	ld (072bbh),a		;82c3	32 bb 72 	2 . r 
	ld hl,082ddh		;82c6	21 dd 82 	! . . 
	ld a,002h		;82c9	3e 02 	> . 
	ld iy,00001h		;82cb	fd 21 01 00 	. ! . . 
	call 01fbeh		;82cf	cd be 1f 	. . . 
	ret			;82d2	c9 	. 
	cp 001h		;82d3	fe 01 	. . 
	defb 0fdh,002h,0fbh	;illegal sequence		;82d5	fd 02 fb 	. . . 
	inc b			;82d8	04 	. 
	rst 30h			;82d9	f7 	. 
	ex af,af'			;82da	08 	. 
	rst 28h			;82db	ef 	. 
	djnz $+2		;82dc	10 00 	. . 
	ld hl,07272h		;82de	21 72 72 	! r r 
	bit 0,(hl)		;82e1	cb 46 	. F 
	jr z,$+34		;82e3	28 20 	(   
	res 0,(hl)		;82e5	cb 86 	. . 
	ld a,(0726eh)		;82e7	3a 6e 72 	: n r 
	bit 1,a		;82ea	cb 4f 	. O 
	ld a,(07274h)		;82ec	3a 74 72 	: t r 
	jr z,$+5		;82ef	28 03 	( . 
	ld a,(07275h)		;82f1	3a 75 72 	: u r 
	dec a			;82f4	3d 	= 
	cp 00ah		;82f5	fe 0a 	. . 
	jr c,$+4		;82f7	38 02 	8 . 
	ld a,009h		;82f9	3e 09 	> . 
	ld hl,08333h		;82fb	21 33 83 	! 3 . 
	ld c,a			;82fe	4f 	O 
	ld b,000h		;82ff	06 00 	. . 
	add hl,bc			;8301	09 	. 
	ld a,(hl)			;8302	7e 	~ 
	jr $+10		;8303	18 08 	. . 
	bit 1,(hl)		;8305	cb 4e 	. N 
	jr z,$+9		;8307	28 07 	( . 
	res 1,(hl)		;8309	cb 8e 	. . 
	ld a,00eh		;830b	3e 0e 	> . 
	call 0ae2fh		;830d	cd 2f ae 	. / . 
	ld hl,07273h		;8310	21 73 72 	! s r 
	bit 7,(hl)		;8313	cb 7e 	. ~ 
	jr z,$+29		;8315	28 1b 	( . 
	ld ix,0722ch		;8317	dd 21 2c 72 	. ! , r 
	ld b,(ix+001h)		;831b	dd 46 01 	. F . 
	ld c,(ix+002h)		;831e	dd 4e 02 	. N . 
	ld d,000h		;8321	16 00 	. . 
	bit 0,(hl)		;8323	cb 46 	. F 
	jr nz,$+4		;8325	20 02 	  . 
	ld d,004h		;8327	16 04 	. . 
	ld a,(hl)			;8329	7e 	~ 
	xor 001h		;832a	ee 01 	. . 
	ld (hl),a			;832c	77 	w 
	ld a,08dh		;832d	3e 8d 	> . 
	call 0b629h		;832f	cd 29 b6 	. ) . 
	ret			;8332	c9 	. 
	ld a,(bc)			;8333	0a 	. 
	dec bc			;8334	0b 	. 
	inc c			;8335	0c 	. 
	dec c			;8336	0d 	. 
	ld a,(bc)			;8337	0a 	. 
	dec bc			;8338	0b 	. 
	inc c			;8339	0c 	. 
	dec c			;833a	0d 	. 
	ld a,(bc)			;833b	0a 	. 
	dec bc			;833c	0b 	. 
	ld de,07000h		;833d	11 00 70 	. . p 
	xor a			;8340	af 	. 
	ld (de),a			;8341	12 	. 
	inc de			;8342	13 	. 
	ld hl,073b0h		;8343	21 b0 73 	! . s 
	sbc hl,de		;8346	ed 52 	. R 
	ld a,h			;8348	7c 	| 
	or l			;8349	b5 	. 
	jr nz,$-10		;834a	20 f4 	  . 
	ld a,001h		;834c	3e 01 	> . 
	ld (073c7h),a		;834e	32 c7 73 	2 . s 
	ld a,000h		;8351	3e 00 	> . 
	ld (073c6h),a		;8353	32 c6 73 	2 . s 
	call 0c958h		;8356	cd 58 c9 	. X . 
	ld a,014h		;8359	3e 14 	> . 
	call 01fc1h		;835b	cd c1 1f 	. . . 
	ld hl,0709eh		;835e	21 9e 70 	! . p 
	ld de,07014h		;8361	11 14 70 	. . p 
	call 01fc7h		;8364	cd c7 1f 	. . . 
	ld hl,07086h		;8367	21 86 70 	! . p 
	ld a,09bh		;836a	3e 9b 	> . 
	ld (hl),a			;836c	77 	w 
	inc hl			;836d	23 	# 
	ld (hl),a			;836e	77 	w 
	jp 08372h		;836f	c3 72 83 	. r . 
	call 083d4h		;8372	cd d4 83 	. . . 
	call 084f8h		;8375	cd f8 84 	. . . 
	call 08828h		;8378	cd 28 88 	. ( . 
	call 088d2h		;837b	cd d2 88 	. . . 
	cp 001h		;837e	fe 01 	. . 
	jr z,$+43		;8380	28 29 	( ) 
	and a			;8382	a7 	. 
	jr nz,$+72		;8383	20 46 	  F 
	call 08fd1h		;8385	cd d1 8f 	. . . 
	and a			;8388	a7 	. 
	jr nz,$+66		;8389	20 40 	  @ 
	call 09459h		;838b	cd 59 94 	. Y . 
	and a			;838e	a7 	. 
	jr nz,$+60		;838f	20 3a 	  : 
	call 0a7f4h		;8391	cd f4 a7 	. . . 
	and a			;8394	a7 	. 
	jr nz,$+22		;8395	20 14 	  . 
	call 09842h		;8397	cd 42 98 	. B . 
	cp 001h		;839a	fe 01 	. . 
	jr z,$+15		;839c	28 0d 	( . 
	and a			;839e	a7 	. 
	jr nz,$+44		;839f	20 2a 	  * 
	call 0a53eh		;83a1	cd 3e a5 	. > . 
	and a			;83a4	a7 	. 
	jr z,$-45		;83a5	28 d1 	( . 
	cp 001h		;83a7	fe 01 	. . 
	jr nz,$+34		;83a9	20 20 	    
	ld ix,0722ch		;83ab	dd 21 2c 72 	. ! , r 
	ld b,005h		;83af	06 05 	. . 
	bit 3,(ix+000h)		;83b1	dd cb 00 5e 	. . . ^ 
	jr nz,$+11		;83b5	20 09 	  . 
	ld de,00005h		;83b7	11 05 00 	. . . 
	add ix,de		;83ba	dd 19 	. . 
	djnz $-11		;83bc	10 f3 	. . 
	jr $+7		;83be	18 05 	. . 
	call 088d2h		;83c0	cd d2 88 	. . . 
	jr $-24		;83c3	18 e6 	. . 
	cp 000h		;83c5	fe 00 	. . 
	jr nz,$+4		;83c7	20 02 	  . 
	ld a,001h		;83c9	3e 01 	> . 
	call 0a931h		;83cb	cd 31 a9 	. 1 . 
	cp 003h		;83ce	fe 03 	. . 
	jr z,$-94		;83d0	28 a0 	( . 
	jr $-93		;83d2	18 a1 	. . 
	call 083dch		;83d4	cd dc 83 	. . . 
	call 08407h		;83d7	cd 07 84 	. . . 
	xor a			;83da	af 	. 
	ret			;83db	c9 	. 
	call 01f7ch		;83dc	cd 7c 1f 	. | . 
	call 01febh		;83df	cd eb 1f 	. . . 
	ld a,(0708ch)		;83e2	3a 8c 70 	: . p 
	and a			;83e5	a7 	. 
	jr z,$+6		;83e6	28 04 	( . 
	cp 009h		;83e8	fe 09 	. . 
	jr c,$+12		;83ea	38 0a 	8 . 
	ld a,(07091h)		;83ec	3a 91 70 	: . p 
	and a			;83ef	a7 	. 
	jr z,$-17		;83f0	28 ed 	( . 
	cp 009h		;83f2	fe 09 	. . 
	jr nc,$-21		;83f4	30 e9 	0 . 
	ld hl,0726eh		;83f6	21 6e 72 	! n r 
	res 0,(hl)		;83f9	cb 86 	. . 
	cp 005h		;83fb	fe 05 	. . 
	jr c,$+6		;83fd	38 04 	8 . 
	set 0,(hl)		;83ff	cb c6 	. . 
	sub 004h		;8401	d6 04 	. . 
	ld (07271h),a		;8403	32 71 72 	2 q r 
	ret			;8406	c9 	. 
	ld bc,00000h		;8407	01 00 00 	. . . 
	call 01fd9h		;840a	cd d9 1f 	. . . 
	ld bc,001c2h		;840d	01 c2 01 	. . . 
	call 01fd9h		;8410	cd d9 1f 	. . . 
	ld bc,00700h		;8413	01 00 07 	. . . 
	call 01fd9h		;8416	cd d9 1f 	. . . 
	xor a			;8419	af 	. 
	ld hl,01900h		;841a	21 00 19 	! . . 
	call 01fb8h		;841d	cd b8 1f 	. . . 
	ld a,001h		;8420	3e 01 	> . 
	ld hl,02000h		;8422	21 00 20 	! .   
	call 01fb8h		;8425	cd b8 1f 	. . . 
	ld a,002h		;8428	3e 02 	> . 
	ld hl,01000h		;842a	21 00 10 	! . . 
	call 01fb8h		;842d	cd b8 1f 	. . . 
	ld a,003h		;8430	3e 03 	> . 
	ld hl,00000h		;8432	21 00 00 	! . . 
	call 01fb8h		;8435	cd b8 1f 	. . . 
	ld a,004h		;8438	3e 04 	> . 
	ld hl,01800h		;843a	21 00 18 	! . . 
	call 01fb8h		;843d	cd b8 1f 	. . . 
	ld hl,00000h		;8440	21 00 00 	! . . 
	ld de,04000h		;8443	11 00 40 	. . @ 
	xor a			;8446	af 	. 
	call 01f82h		;8447	cd 82 1f 	. . . 
	ld ix,0c700h		;844a	dd 21 00 c7 	. ! . . 
	ld a,(ix+000h)		;844e	dd 7e 00 	. ~ . 
	and a			;8451	a7 	. 
	jr z,$+35		;8452	28 21 	( ! 
	ld b,000h		;8454	06 00 	. . 
	ld c,a			;8456	4f 	O 
	push bc			;8457	c5 	. 
	pop iy		;8458	fd e1 	. . 
	ld d,000h		;845a	16 00 	. . 
	ld e,(ix+001h)		;845c	dd 5e 01 	. ^ . 
	ld l,(ix+002h)		;845f	dd 6e 02 	. n . 
	ld h,(ix+003h)		;8462	dd 66 03 	. f . 
	ld a,003h		;8465	3e 03 	> . 
	push ix		;8467	dd e5 	. . 
	call 01fbeh		;8469	cd be 1f 	. . . 
	pop ix		;846c	dd e1 	. . 
	ld bc,00004h		;846e	01 04 00 	. . . 
	add ix,bc		;8471	dd 09 	. . 
	jr $-37		;8473	18 d9 	. . 
	ld hl,(0006ch)		;8475	2a 6c 00 	* l . 
	ld de,000d8h		;8478	11 d8 00 	. . . 
	ld iy,0000ah		;847b	fd 21 0a 00 	. ! . . 
	ld a,003h		;847f	3e 03 	> . 
	call 01fbeh		;8481	cd be 1f 	. . . 
	ld hl,(0006ah)		;8484	2a 6a 00 	* j . 
	ld de,000e2h		;8487	11 e2 00 	. . . 
	ld iy,0001ah		;848a	fd 21 1a 00 	. ! . . 
	ld a,003h		;848e	3e 03 	> . 
	call 01fbeh		;8490	cd be 1f 	. . . 
	ld hl,(0006ch)		;8493	2a 6c 00 	* l . 
	ld bc,0ffe0h		;8496	01 e0 ff 	. . . 
	add hl,bc			;8499	09 	. 
	ld de,000fch		;849a	11 fc 00 	. . . 
	ld iy,00003h		;849d	fd 21 03 00 	. ! . . 
	ld a,003h		;84a1	3e 03 	> . 
	call 01fbeh		;84a3	cd be 1f 	. . . 
	ld hl,(0006ch)		;84a6	2a 6c 00 	* l . 
	ld bc,0ff88h		;84a9	01 88 ff 	. . . 
	add hl,bc			;84ac	09 	. 
	ld de,000ffh		;84ad	11 ff 00 	. . . 
	ld iy,00001h		;84b0	fd 21 01 00 	. ! . . 
	ld a,003h		;84b4	3e 03 	> . 
	call 01fbeh		;84b6	cd be 1f 	. . . 
	ld a,01bh		;84b9	3e 1b 	> . 
	push af			;84bb	f5 	. 
	call 0ad01h		;84bc	cd 01 ad 	. . . 
	pop af			;84bf	f1 	. 
	dec a			;84c0	3d 	= 
	jp p,084bbh		;84c1	f2 bb 84 	. . . 
	ld hl,0c440h		;84c4	21 40 c4 	! @ . 
	ld de,00060h		;84c7	11 60 00 	. ` . 
	ld iy,00040h		;84ca	fd 21 40 00 	. ! @ . 
	ld a,001h		;84ce	3e 01 	> . 
	call 01fbeh		;84d0	cd be 1f 	. . . 
	ld hl,0c640h		;84d3	21 40 c6 	! @ . 
	ld de,000c0h		;84d6	11 c0 00 	. . . 
	ld iy,00018h		;84d9	fd 21 18 00 	. ! . . 
	ld a,001h		;84dd	3e 01 	> . 
	call 01fbeh		;84df	cd be 1f 	. . . 
	ld hl,0bf7bh		;84e2	21 7b bf 	! { . 
	ld de,00000h		;84e5	11 00 00 	. . . 
	ld iy,00020h		;84e8	fd 21 20 00 	. !   . 
	ld a,004h		;84ec	3e 04 	> . 
	call 01fbeh		;84ee	cd be 1f 	. . . 
	ld bc,001e2h		;84f1	01 e2 01 	. . . 
	call 01fd9h		;84f4	cd d9 1f 	. . . 
	ret			;84f7	c9 	. 
	push af			;84f8	f5 	. 
	ld hl,0726eh		;84f9	21 6e 72 	! n r 
	set 7,(hl)		;84fc	cb fe 	. . 
	bit 7,(hl)		;84fe	cb 7e 	. ~ 
	jr nz,$-2		;8500	20 fc 	  . 
	pop af			;8502	f1 	. 
	push af			;8503	f5 	. 
	and a			;8504	a7 	. 
	jr nz,$+5		;8505	20 03 	  . 
	call 0851ch		;8507	cd 1c 85 	. . . 
	call 08585h		;850a	cd 85 85 	. . . 
	pop af			;850d	f1 	. 
	cp 002h		;850e	fe 02 	. . 
	jr z,$+5		;8510	28 03 	( . 
	call 08676h		;8512	cd 76 86 	. v . 
	call 086c5h		;8515	cd c5 86 	. . . 
	call 087f4h		;8518	cd f4 87 	. . . 
	ret			;851b	c9 	. 
	ld hl,00000h		;851c	21 00 00 	! . . 
	ld (0727dh),hl		;851f	22 7d 72 	" } r 
	ld (0727fh),hl		;8522	22 7f 72 	"  r 
	ld a,001h		;8525	3e 01 	> . 
	ld (07274h),a		;8527	32 74 72 	2 t r 
	ld (07275h),a		;852a	32 75 72 	2 u r 
	xor a			;852d	af 	. 
	ld (0727ah),a		;852e	32 7a 72 	2 z r 
	ld (0727bh),a		;8531	32 7b 72 	2 { r 
	ld a,(07271h)		;8534	3a 71 72 	: q r 
	cp 002h		;8537	fe 02 	. . 
	ld a,003h		;8539	3e 03 	> . 
	jr nc,$+4		;853b	30 02 	0 . 
	ld a,005h		;853d	3e 05 	> . 
	ld (07276h),a		;853f	32 76 72 	2 v r 
	ld (07277h),a		;8542	32 77 72 	2 w r 
	ld a,(0726eh)		;8545	3a 6e 72 	: n r 
	and 001h		;8548	e6 01 	. . 
	ld (0726eh),a		;854a	32 6e 72 	2 n r 
	ld a,001h		;854d	3e 01 	> . 
	call 0b286h		;854f	cd 86 b2 	. . . 
	ld hl,0718ah		;8552	21 8a 71 	! . q 
	ld de,03400h		;8555	11 00 34 	. . 4 
	ld bc,000d4h		;8558	01 d4 00 	. . . 
	call 01fdfh		;855b	cd df 1f 	. . . 
	ld hl,0718ah		;855e	21 8a 71 	! . q 
	ld de,03600h		;8561	11 00 36 	. . 6 
	ld bc,000d4h		;8564	01 d4 00 	. . . 
	call 01fdfh		;8567	cd df 1f 	. . . 
	call 0866bh		;856a	cd 6b 86 	. k . 
	ld hl,072b8h		;856d	21 b8 72 	! . r 
	ld b,00bh		;8570	06 0b 	. . 
	xor a			;8572	af 	. 
	ld (hl),a			;8573	77 	w 
	inc hl			;8574	23 	# 
	djnz $-2		;8575	10 fc 	. . 
	ld a,008h		;8577	3e 08 	> . 
	ld (072bah),a		;8579	32 ba 72 	2 . r 
	ld a,007h		;857c	3e 07 	> . 
	ld (07278h),a		;857e	32 78 72 	2 x r 
	ld (07279h),a		;8581	32 79 72 	2 y r 
	ret			;8584	c9 	. 
	xor a			;8585	af 	. 
	ld (072d9h),a		;8586	32 d9 72 	2 . r 
	ld (072ddh),a		;8589	32 dd 72 	2 . r 
	ld (07272h),a		;858c	32 72 72 	2 r r 
	ld (07273h),a		;858f	32 73 72 	2 s r 
	ld hl,0726eh		;8592	21 6e 72 	! n r 
	res 6,(hl)		;8595	cb b6 	. . 
	ld de,03400h		;8597	11 00 34 	. . 4 
	ld a,(0726eh)		;859a	3a 6e 72 	: n r 
	bit 1,a		;859d	cb 4f 	. O 
	jr z,$+5		;859f	28 03 	( . 
	ld de,03600h		;85a1	11 00 36 	. . 6 
	ld hl,0718ah		;85a4	21 8a 71 	! . q 
	ld bc,000d4h		;85a7	01 d4 00 	. . . 
	call 01fe2h		;85aa	cd e2 1f 	. . . 
	xor a			;85ad	af 	. 
	ld (07139h),a		;85ae	32 39 71 	2 9 q 
	ld hl,0713ah		;85b1	21 3a 71 	! : q 
	ld b,050h		;85b4	06 50 	. P 
	ld (hl),a			;85b6	77 	w 
	inc hl			;85b7	23 	# 
	djnz $-2		;85b8	10 fc 	. . 
	ld a,(0726eh)		;85ba	3a 6e 72 	: n r 
	bit 1,a		;85bd	cb 4f 	. O 
	ld a,(07274h)		;85bf	3a 74 72 	: t r 
	jr z,$+5		;85c2	28 03 	( . 
	ld a,(07275h)		;85c4	3a 75 72 	: u r 
	cp 00bh		;85c7	fe 0b 	. . 
	jr c,$+6		;85c9	38 04 	8 . 
	sub 00ah		;85cb	d6 0a 	. . 
	jr $-6		;85cd	18 f8 	. . 
	dec a			;85cf	3d 	= 
	add a,a			;85d0	87 	. 
	ld e,a			;85d1	5f 	_ 
	ld d,000h		;85d2	16 00 	. . 
	ld ix,0c007h		;85d4	dd 21 07 c0 	. ! . . 
	add ix,de		;85d8	dd 19 	. . 
	ld l,(ix+000h)		;85da	dd 6e 00 	. n . 
	ld h,(ix+001h)		;85dd	dd 66 01 	. f . 
	ld a,(hl)			;85e0	7e 	~ 
	ld (07139h),a		;85e1	32 39 71 	2 9 q 
	ld c,(hl)			;85e4	4e 	N 
	ld b,000h		;85e5	06 00 	. . 
	inc hl			;85e7	23 	# 
	ld de,0713ah		;85e8	11 3a 71 	. : q 
	ldir		;85eb	ed b0 	. . 
	ld hl,0709eh		;85ed	21 9e 70 	! . p 
	ld de,07014h		;85f0	11 14 70 	. . p 
	call 01fc7h		;85f3	cd c7 1f 	. . . 
	ld a,(0726eh)		;85f6	3a 6e 72 	: n r 
	bit 1,a		;85f9	cb 4f 	. O 
	ld a,(07274h)		;85fb	3a 74 72 	: t r 
	jr z,$+5		;85fe	28 03 	( . 
	ld a,(07275h)		;8600	3a 75 72 	: u r 
	cp 00bh		;8603	fe 0b 	. . 
	jr c,$+6		;8605	38 04 	8 . 
	sub 00ah		;8607	d6 0a 	. . 
	jr $-6		;8609	18 f8 	. . 
	dec a			;860b	3d 	= 
	add a,a			;860c	87 	. 
	ld c,a			;860d	4f 	O 
	ld b,000h		;860e	06 00 	. . 
	ld iy,0bf67h		;8610	fd 21 67 bf 	. ! g . 
	add iy,bc		;8614	fd 09 	. . 
	ld l,(iy+000h)		;8616	fd 6e 00 	. n . 
	ld h,(iy+001h)		;8619	fd 66 01 	. f . 
	ld de,00000h		;861c	11 00 00 	. . . 
	ld iy,0000ch		;861f	fd 21 0c 00 	. ! . . 
	ld a,004h		;8623	3e 04 	> . 
	call 01fbeh		;8625	cd be 1f 	. . . 
	ld hl,072c3h		;8628	21 c3 72 	! . r 
	ld b,016h		;862b	06 16 	. . 
	xor a			;862d	af 	. 
	ld (hl),a			;862e	77 	w 
	inc hl			;862f	23 	# 
	djnz $-2		;8630	10 fc 	. . 
	call 0866bh		;8632	cd 6b 86 	. k . 
	ld a,(072c1h)		;8635	3a c1 72 	: . r 
	and 007h		;8638	e6 07 	. . 
	ld (072c1h),a		;863a	32 c1 72 	2 . r 
	ld a,(072bah)		;863d	3a ba 72 	: . r 
	and 03fh		;8640	e6 3f 	. ? 
	ld (072bah),a		;8642	32 ba 72 	2 . r 
	ld hl,07278h		;8645	21 78 72 	! x r 
	ld a,(0726eh)		;8648	3a 6e 72 	: n r 
	and 003h		;864b	e6 03 	. . 
	cp 003h		;864d	fe 03 	. . 
	jr nz,$+3		;864f	20 01 	  . 
	inc hl			;8651	23 	# 
	ld a,(hl)			;8652	7e 	~ 
	cp 007h		;8653	fe 07 	. . 
	jp nc,0866ah		;8655	d2 6a 86 	. j . 
	ld iy,072b2h		;8658	fd 21 b2 72 	. ! . r 
	ld (iy+004h),0c0h		;865c	fd 36 04 c0 	. 6 . . 
	ld de,0fffah		;8660	11 fa ff 	. . . 
	add iy,de		;8663	fd 19 	. . 
	inc a			;8665	3c 	< 
	cp 007h		;8666	fe 07 	. . 
	jr nz,$-12		;8668	20 f2 	  . 
	ret			;866a	c9 	. 
	ld hl,0728ah		;866b	21 8a 72 	! . r 
	ld b,02eh		;866e	06 2e 	. . 
	xor a			;8670	af 	. 
	ld (hl),a			;8671	77 	w 
	inc hl			;8672	23 	# 
	djnz $-2		;8673	10 fc 	. . 
	ret			;8675	c9 	. 
	ld hl,01000h		;8676	21 00 10 	! . . 
	ld de,00300h		;8679	11 00 03 	. . . 
	ld a,000h		;867c	3e 00 	> . 
	call 01f82h		;867e	cd 82 1f 	. . . 
	ld hl,01900h		;8681	21 00 19 	! . . 
	ld de,00080h		;8684	11 80 00 	. . . 
	ld a,000h		;8687	3e 00 	> . 
	call 01f82h		;8689	cd 82 1f 	. . . 
	ld hl,070e9h		;868c	21 e9 70 	! . p 
	ld b,050h		;868f	06 50 	. P 
	ld (hl),000h		;8691	36 00 	6 . 
	inc hl			;8693	23 	# 
	djnz $-3		;8694	10 fb 	. . 
	ld a,(0726eh)		;8696	3a 6e 72 	: n r 
	bit 1,a		;8699	cb 4f 	. O 
	ld a,004h		;869b	3e 04 	> . 
	jr z,$+4		;869d	28 02 	( . 
	ld a,005h		;869f	3e 05 	> . 
	call 0ae2fh		;86a1	cd 2f ae 	. / . 
	ld bc,001e2h		;86a4	01 e2 01 	. . . 
	call 01fd9h		;86a7	cd d9 1f 	. . . 
	ld hl,000b4h		;86aa	21 b4 00 	! . . 
	xor a			;86ad	af 	. 
	call 01fcdh		;86ae	cd cd 1f 	. . . 
	push af			;86b1	f5 	. 
	pop af			;86b2	f1 	. 
	push af			;86b3	f5 	. 
	call 01fd0h		;86b4	cd d0 1f 	. . . 
	and a			;86b7	a7 	. 
	jr z,$-6		;86b8	28 f8 	( . 
	pop af			;86ba	f1 	. 
	ld hl,0726eh		;86bb	21 6e 72 	! n r 
	set 7,(hl)		;86be	cb fe 	. . 
	bit 7,(hl)		;86c0	cb 7e 	. ~ 
	jr nz,$-2		;86c2	20 fc 	  . 
	ret			;86c4	c9 	. 
	ld hl,01000h		;86c5	21 00 10 	! . . 
	ld de,00300h		;86c8	11 00 03 	. . . 
	ld a,000h		;86cb	3e 00 	> . 
	call 01f82h		;86cd	cd 82 1f 	. . . 
	ld hl,01900h		;86d0	21 00 19 	! . . 
	ld de,00080h		;86d3	11 80 00 	. . . 
	ld a,000h		;86d6	3e 00 	> . 
	call 01f82h		;86d8	cd 82 1f 	. . . 
	ld hl,070e9h		;86db	21 e9 70 	! . p 
	ld b,050h		;86de	06 50 	. P 
	ld (hl),000h		;86e0	36 00 	6 . 
	inc hl			;86e2	23 	# 
	djnz $-3		;86e3	10 fb 	. . 
	ld a,0a0h		;86e5	3e a0 	> . 
	push af			;86e7	f5 	. 
	call 0b19ch		;86e8	cd 9c b1 	. . . 
	pop af			;86eb	f1 	. 
	dec a			;86ec	3d 	= 
	jr nz,$-6		;86ed	20 f8 	  . 
	ld a,001h		;86ef	3e 01 	> . 
	call 0ae2fh		;86f1	cd 2f ae 	. / . 
	xor a			;86f4	af 	. 
	call 0b5a6h		;86f5	cd a6 b5 	. . . 
	ld a,(0726eh)		;86f8	3a 6e 72 	: n r 
	bit 0,a		;86fb	cb 47 	. G 
	jr z,$+12		;86fd	28 0a 	( . 
	ld a,00fh		;86ff	3e 0f 	> . 
	call 0ae2fh		;8701	cd 2f ae 	. / . 
	ld a,001h		;8704	3e 01 	> . 
	call 0b5a6h		;8706	cd a6 b5 	. . . 
	ld a,(0726eh)		;8709	3a 6e 72 	: n r 
	bit 1,a		;870c	cb 4f 	. O 
	ld a,(07274h)		;870e	3a 74 72 	: t r 
	jr z,$+5		;8711	28 03 	( . 
	ld a,(07275h)		;8713	3a 75 72 	: u r 
	ld hl,072e7h		;8716	21 e7 72 	! . r 
	ld d,0d8h		;8719	16 d8 	. . 
	ld iy,00001h		;871b	fd 21 01 00 	. ! . . 
	cp 00ah		;871f	fe 0a 	. . 
	jr nc,$+7		;8721	30 05 	0 . 
	add a,0d8h		;8723	c6 d8 	. . 
	ld (hl),a			;8725	77 	w 
	jr $+19		;8726	18 11 	. . 
	cp 00ah		;8728	fe 0a 	. . 
	jr c,$+7		;872a	38 05 	8 . 
	sub 00ah		;872c	d6 0a 	. . 
	inc d			;872e	14 	. 
	jr $-7		;872f	18 f7 	. . 
	inc iy		;8731	fd 23 	. # 
	ld (hl),d			;8733	72 	r 
	inc hl			;8734	23 	# 
	add a,0d8h		;8735	c6 d8 	. . 
	ld (hl),a			;8737	77 	w 
	dec hl			;8738	2b 	+ 
	ld de,0003dh		;8739	11 3d 00 	. = . 
	ld a,002h		;873c	3e 02 	> . 
	call 01fbeh		;873e	cd be 1f 	. . . 
	ld a,002h		;8741	3e 02 	> . 
	call 0ae2fh		;8743	cd 2f ae 	. / . 
	ld hl,072b8h		;8746	21 b8 72 	! . r 
	ld a,(0726eh)		;8749	3a 6e 72 	: n r 
	bit 1,a		;874c	cb 4f 	. O 
	jr z,$+5		;874e	28 03 	( . 
	ld hl,072b9h		;8750	21 b9 72 	! . r 
	ld de,0012bh		;8753	11 2b 01 	. + . 
	ld bc,00000h		;8756	01 00 00 	. . . 
	ld a,(hl)			;8759	7e 	~ 
	push hl			;875a	e5 	. 
	ld hl,087e8h		;875b	21 e8 87 	! . . 
	and d			;875e	a2 	. 
	jr z,$+5		;875f	28 03 	( . 
	ld hl,087edh		;8761	21 ed 87 	! . . 
	add hl,bc			;8764	09 	. 
	push bc			;8765	c5 	. 
	push de			;8766	d5 	. 
	ld d,000h		;8767	16 00 	. . 
	ld iy,00001h		;8769	fd 21 01 00 	. ! . . 
	ld a,002h		;876d	3e 02 	> . 
	call 01fbeh		;876f	cd be 1f 	. . . 
	pop de			;8772	d1 	. 
	pop bc			;8773	c1 	. 
	pop hl			;8774	e1 	. 
	inc e			;8775	1c 	. 
	inc e			;8776	1c 	. 
	rlc d		;8777	cb 02 	. . 
	inc c			;8779	0c 	. 
	ld a,c			;877a	79 	y 
	cp 005h		;877b	fe 05 	. . 
	jr nz,$-36		;877d	20 da 	  . 
	ld a,(0726eh)		;877f	3a 6e 72 	: n r 
	bit 1,a		;8782	cb 4f 	. O 
	ld hl,07276h		;8784	21 76 72 	! v r 
	jr z,$+5		;8787	28 03 	( . 
	ld hl,07277h		;8789	21 77 72 	! w r 
	ld b,(hl)			;878c	46 	F 
	ld de,00035h		;878d	11 35 00 	. 5 . 
	dec b			;8790	05 	. 
	jr z,$+40		;8791	28 26 	( & 
	push bc			;8793	c5 	. 
	push de			;8794	d5 	. 
	ld hl,087f2h		;8795	21 f2 87 	! . . 
	ld iy,00001h		;8798	fd 21 01 00 	. ! . . 
	ld a,002h		;879c	3e 02 	> . 
	call 01fbeh		;879e	cd be 1f 	. . . 
	pop hl			;87a1	e1 	. 
	push hl			;87a2	e5 	. 
	ld de,00020h		;87a3	11 20 00 	.   . 
	add hl,de			;87a6	19 	. 
	ex de,hl			;87a7	eb 	. 
	ld hl,087f3h		;87a8	21 f3 87 	! . . 
	ld iy,00001h		;87ab	fd 21 01 00 	. ! . . 
	ld a,002h		;87af	3e 02 	> . 
	call 01fbeh		;87b1	cd be 1f 	. . . 
	pop de			;87b4	d1 	. 
	pop bc			;87b5	c1 	. 
	inc de			;87b6	13 	. 
	jr $-39		;87b7	18 d7 	. . 
	ld a,003h		;87b9	3e 03 	> . 
	call 0ae2fh		;87bb	cd 2f ae 	. / . 
	ld b,005h		;87be	06 05 	. . 
	ld iy,0722ch		;87c0	fd 21 2c 72 	. ! , r 
	ld a,00ch		;87c4	3e 0c 	> . 
	bit 7,(iy+000h)		;87c6	fd cb 00 7e 	. . . ~ 
	jr z,$+21		;87ca	28 13 	( . 
	push bc			;87cc	c5 	. 
	push ix		;87cd	dd e5 	. . 
	push af			;87cf	f5 	. 
	ld b,(iy+001h)		;87d0	fd 46 01 	. F . 
	ld c,(iy+002h)		;87d3	fd 4e 02 	. N . 
	ld d,001h		;87d6	16 01 	. . 
	call 0b629h		;87d8	cd 29 b6 	. ) . 
	pop af			;87db	f1 	. 
	pop ix		;87dc	dd e1 	. . 
	pop bc			;87de	c1 	. 
	ld de,00005h		;87df	11 05 00 	. . . 
	add iy,de		;87e2	fd 19 	. . 
	inc a			;87e4	3c 	< 
	djnz $-31		;87e5	10 df 	. . 
	ret			;87e7	c9 	. 
	ld (03433h),a		;87e8	32 33 34 	2 3 4 
	dec (hl)			;87eb	35 	5 
	ld (hl),048h		;87ec	36 48 	6 H 
	ld c,c			;87ee	49 	I 
	ld c,d			;87ef	4a 	J 
	ld c,e			;87f0	4b 	K 
	ld c,h			;87f1	4c 	L 
	ld a,b			;87f2	78 	x 
	ld a,c			;87f3	79 	y 
	ld iy,07281h		;87f4	fd 21 81 72 	. ! . r 
	xor a			;87f8	af 	. 
	ld (iy+006h),a		;87f9	fd 77 06 	. w . 
	ld (iy+007h),a		;87fc	fd 77 07 	. w . 
	ld a,001h		;87ff	3e 01 	> . 
	ld (iy+001h),a		;8801	fd 77 01 	. w . 
	ld (iy+005h),a		;8804	fd 77 05 	. w . 
	ld (iy+003h),0b0h		;8807	fd 36 03 b0 	. 6 . . 
	ld (iy+004h),078h		;880b	fd 36 04 78 	. 6 . x 
	ld (iy+000h),0c0h		;880f	fd 36 00 c0 	. 6 . . 
	ld bc,001e2h		;8813	01 e2 01 	. . . 
	call 01fd9h		;8816	cd d9 1f 	. . . 
	call 0c960h		;8819	cd 60 c9 	. ` . 
	ld hl,00001h		;881c	21 01 00 	! . . 
	xor a			;881f	af 	. 
	call 01fcdh		;8820	cd cd 1f 	. . . 
	ld (07283h),a		;8823	32 83 72 	2 . r 
	pop af			;8826	f1 	. 
	ret			;8827	c9 	. 
	ld a,(0726eh)		;8828	3a 6e 72 	: n r 
	bit 1,a		;882b	cb 4f 	. O 
	ld a,(0708ch)		;882d	3a 8c 70 	: . p 
	jr z,$+5		;8830	28 03 	( . 
	ld a,(07091h)		;8832	3a 91 70 	: . p 
	cp 00ah		;8835	fe 0a 	. . 
	jp nz,088d0h		;8837	c2 d0 88 	. . . 
	ld hl,0726eh		;883a	21 6e 72 	! n r 
	set 7,(hl)		;883d	cb fe 	. . 
	bit 7,(hl)		;883f	cb 7e 	. ~ 
	jr nz,$-2		;8841	20 fc 	  . 
	set 5,(hl)		;8843	cb ee 	. . 
	xor a			;8845	af 	. 
	ld hl,01900h		;8846	21 00 19 	! . . 
	ld de,00080h		;8849	11 80 00 	. . . 
	call 01f82h		;884c	cd 82 1f 	. . . 
	ld a,002h		;884f	3e 02 	> . 
	ld hl,03800h		;8851	21 00 38 	! . 8 
	call 01fb8h		;8854	cd b8 1f 	. . . 
	ld hl,07020h		;8857	21 20 70 	!   p 
	ld de,03b00h		;885a	11 00 3b 	. . ; 
	ld bc,0005dh		;885d	01 5d 00 	. ] . 
	call 01fdfh		;8860	cd df 1f 	. . . 
	ld bc,001e2h		;8863	01 e2 01 	. . . 
	call 01fd9h		;8866	cd d9 1f 	. . . 
	call 0ca0ah		;8869	cd 0a ca 	. . . 
	ld b,002h		;886c	06 02 	. . 
	ld hl,00000h		;886e	21 00 00 	! . . 
	dec hl			;8871	2b 	+ 
	ld a,l			;8872	7d 	} 
	or h			;8873	b4 	. 
	jr nz,$-3		;8874	20 fb 	  . 
	djnz $-8		;8876	10 f6 	. . 
	ld a,(0726eh)		;8878	3a 6e 72 	: n r 
	bit 1,a		;887b	cb 4f 	. O 
	ld a,(0708ch)		;887d	3a 8c 70 	: . p 
	jr z,$+5		;8880	28 03 	( . 
	ld a,(07091h)		;8882	3a 91 70 	: . p 
	cp 00ah		;8885	fe 0a 	. . 
	jr nz,$-15		;8887	20 ef 	  . 
	call 0c958h		;8889	cd 58 c9 	. X . 
	ld hl,0726eh		;888c	21 6e 72 	! n r 
	set 7,(hl)		;888f	cb fe 	. . 
	bit 7,(hl)		;8891	cb 7e 	. ~ 
	jr nz,$-2		;8893	20 fc 	  . 
	set 4,(hl)		;8895	cb e6 	. . 
	ld a,002h		;8897	3e 02 	> . 
	ld hl,01000h		;8899	21 00 10 	! . . 
	call 01fb8h		;889c	cd b8 1f 	. . . 
	ld bc,001e2h		;889f	01 e2 01 	. . . 
	call 01fd9h		;88a2	cd d9 1f 	. . . 
	ld b,004h		;88a5	06 04 	. . 
	ld hl,00000h		;88a7	21 00 00 	! . . 
	dec hl			;88aa	2b 	+ 
	ld a,l			;88ab	7d 	} 
	or h			;88ac	b4 	. 
	jr nz,$-3		;88ad	20 fb 	  . 
	djnz $-8		;88af	10 f6 	. . 
	ld hl,0726eh		;88b1	21 6e 72 	! n r 
	set 7,(hl)		;88b4	cb fe 	. . 
	bit 7,(hl)		;88b6	cb 7e 	. ~ 
	jr nz,$-2		;88b8	20 fc 	  . 
	ld a,(hl)			;88ba	7e 	~ 
	and 0cfh		;88bb	e6 cf 	. . 
	ld (hl),a			;88bd	77 	w 
	ld hl,07020h		;88be	21 20 70 	!   p 
	ld de,03b00h		;88c1	11 00 3b 	. . ; 
	ld bc,0005dh		;88c4	01 5d 00 	. ] . 
	call 01fe2h		;88c7	cd e2 1f 	. . . 
	ld bc,001e2h		;88ca	01 e2 01 	. . . 
	call 01fd9h		;88cd	cd d9 1f 	. . . 
	ret			;88d0	c9 	. 
	nop			;88d1	00 	. 
	call 0895ah		;88d2	cd 5a 89 	. Z . 
	xor a			;88d5	af 	. 
	bit 7,(iy+000h)		;88d6	fd cb 00 7e 	. . . ~ 
	jr z,$+112		;88da	28 6e 	( n 
	ld a,(iy+000h)		;88dc	fd 7e 00 	. ~ . 
	bit 3,a		;88df	cb 5f 	. _ 
	jr nz,$+10		;88e1	20 08 	  . 
	xor a			;88e3	af 	. 
	call 08e10h		;88e4	cd 10 8e 	. . . 
	jr z,$+99		;88e7	28 61 	( a 
	jr $+88		;88e9	18 56 	. V 
	ld a,(iy+003h)		;88eb	fd 7e 03 	. ~ . 
	call 01fd0h		;88ee	cd d0 1f 	. . . 
	and a			;88f1	a7 	. 
	jr z,$+88		;88f2	28 56 	( V 
	ld a,(iy+000h)		;88f4	fd 7e 00 	. ~ . 
	bit 6,a		;88f7	cb 77 	. w 
	jr z,$+7		;88f9	28 05 	( . 
	call 08fb0h		;88fb	cd b0 8f 	. . . 
	jr nz,$+67		;88fe	20 41 	  A 
	ld a,(iy+000h)		;8900	fd 7e 00 	. ~ . 
	bit 4,a		;8903	cb 67 	. g 
	jr z,$+11		;8905	28 09 	( . 
	push iy		;8907	fd e5 	. . 
	call 0c9c0h		;8909	cd c0 c9 	. . . 
	pop iy		;890c	fd e1 	. . 
	jr $+6		;890e	18 04 	. . 
	bit 5,a		;8910	cb 6f 	. o 
	jr nz,$+35		;8912	20 21 	  ! 
	ld a,(iy+004h)		;8914	fd 7e 04 	. ~ . 
	ld b,a			;8917	47 	G 
	and 0cfh		;8918	e6 cf 	. . 
	ld c,a			;891a	4f 	O 
	ld a,b			;891b	78 	x 
	add a,010h		;891c	c6 10 	. . 
	and 030h		;891e	e6 30 	. 0 
	or c			;8920	b1 	. 
	ld (iy+004h),a		;8921	fd 77 04 	. w . 
	and 030h		;8924	e6 30 	. 0 
	jr z,$+4		;8926	28 02 	( . 
	jr $+25		;8928	18 17 	. . 
	call 089d1h		;892a	cd d1 89 	. . . 
	call 08a04h		;892d	cd 04 8a 	. . . 
	call 08d8eh		;8930	cd 8e 8d 	. . . 
	jr $+18		;8933	18 10 	. . 
	push iy		;8935	fd e5 	. . 
	call 0c9bbh		;8937	cd bb c9 	. . . 
	pop iy		;893a	fd e1 	. . 
	call 08a52h		;893c	cd 52 8a 	. R . 
	jr z,$+6		;893f	28 04 	( . 
	call 08972h		;8941	cd 72 89 	. r . 
	xor a			;8944	af 	. 
	push af			;8945	f5 	. 
	call 0899ah		;8946	cd 9a 89 	. . . 
	pop af			;8949	f1 	. 
	push af			;894a	f5 	. 
	ld a,(0722ah)		;894b	3a 2a 72 	: * r 
	inc a			;894e	3c 	< 
	cp 005h		;894f	fe 05 	. . 
	jr c,$+3		;8951	38 01 	8 . 
	xor a			;8953	af 	. 
	ld (0722ah),a		;8954	32 2a 72 	2 * r 
	pop af			;8957	f1 	. 
	and a			;8958	a7 	. 
	ret			;8959	c9 	. 
	ld iy,0722ch		;895a	fd 21 2c 72 	. ! , r 
	ld hl,0896ch		;895e	21 6c 89 	! l . 
	ld a,(0722ah)		;8961	3a 2a 72 	: * r 
	ld c,a			;8964	4f 	O 
	ld b,000h		;8965	06 00 	. . 
	add hl,bc			;8967	09 	. 
	ld c,(hl)			;8968	4e 	N 
	add iy,bc		;8969	fd 09 	. . 
	ret			;896b	c9 	. 
	nop			;896c	00 	. 
	dec b			;896d	05 	. 
	ld a,(bc)			;896e	0a 	. 
	rrca			;896f	0f 	. 
	inc d			;8970	14 	. 
	add hl,de			;8971	19 	. 
	ld hl,0000fh		;8972	21 0f 00 	! . . 
	ld a,(iy+000h)		;8975	fd 7e 00 	. ~ . 
	bit 6,a		;8978	cb 77 	. w 
	jr nz,$+24		;897a	20 16 	  . 
	ld hl,00004h		;897c	21 04 00 	! . . 
	bit 5,a		;897f	cb 6f 	. o 
	jr nz,$+17		;8981	20 0f 	  . 
	ld hl,00019h		;8983	21 19 00 	! . . 
	ld a,(iy+004h)		;8986	fd 7e 04 	. ~ . 
	and 030h		;8989	e6 30 	. 0 
	cp 020h		;898b	fe 20 	.   
	jr $+5		;898d	18 03 	. . 
	ld hl,00026h		;898f	21 26 00 	! & . 
	xor a			;8992	af 	. 
	call 01fcdh		;8993	cd cd 1f 	. . . 
	ld (iy+003h),a		;8996	fd 77 03 	. w . 
	ret			;8999	c9 	. 
	ld a,(iy+004h)		;899a	fd 7e 04 	. ~ . 
	rrca			;899d	0f 	. 
	rrca			;899e	0f 	. 
	rrca			;899f	0f 	. 
	rrca			;89a0	0f 	. 
	and 003h		;89a1	e6 03 	. . 
	ld d,a			;89a3	57 	W 
	ld b,(iy+001h)		;89a4	fd 46 01 	. F . 
	ld c,(iy+002h)		;89a7	fd 4e 02 	. N . 
	ld a,(iy+000h)		;89aa	fd 7e 00 	. ~ . 
	bit 6,a		;89ad	cb 77 	. w 
	jr z,$+18		;89af	28 10 	( . 
	and 007h		;89b1	e6 07 	. . 
	cp 002h		;89b3	fe 02 	. . 
	jr z,$+12		;89b5	28 0a 	( . 
	cp 001h		;89b7	fe 01 	. . 
	jr nz,$+6		;89b9	20 04 	  . 
	dec c			;89bb	0d 	. 
	dec c			;89bc	0d 	. 
	jr $+4		;89bd	18 02 	. . 
	inc c			;89bf	0c 	. 
	inc c			;89c0	0c 	. 
	ld a,d			;89c1	7a 	z 
	and a			;89c2	a7 	. 
	jr nz,$+5		;89c3	20 03 	  . 
	ld bc,00808h		;89c5	01 08 08 	. . . 
	ld a,(0722ah)		;89c8	3a 2a 72 	: * r 
	add a,00ch		;89cb	c6 0c 	. . 
	call 0b629h		;89cd	cd 29 b6 	. ) . 
	ret			;89d0	c9 	. 
	push iy		;89d1	fd e5 	. . 
	ld a,(iy+004h)		;89d3	fd 7e 04 	. ~ . 
	and 00fh		;89d6	e6 0f 	. . 
	jr z,$+17		;89d8	28 0f 	( . 
	dec a			;89da	3d 	= 
	add a,a			;89db	87 	. 
	ld c,a			;89dc	4f 	O 
	ld b,000h		;89dd	06 00 	. . 
	ld hl,089ech		;89df	21 ec 89 	! . . 
	add hl,bc			;89e2	09 	. 
	ld e,(hl)			;89e3	5e 	^ 
	inc hl			;89e4	23 	# 
	ld d,(hl)			;89e5	56 	V 
	call 0b601h		;89e6	cd 01 b6 	. . . 
	pop iy		;89e9	fd e1 	. . 
	ret			;89eb	c9 	. 
	ld h,h			;89ec	64 	d 
	nop			;89ed	00 	. 
	ret z			;89ee	c8 	. 
	nop			;89ef	00 	. 
	sub b			;89f0	90 	. 
	ld bc,00258h		;89f1	01 58 02 	. X . 
	jr nz,$+5		;89f4	20 03 	  . 
	ret pe			;89f6	e8 	. 
	inc bc			;89f7	03 	. 
	or b			;89f8	b0 	. 
	inc b			;89f9	04 	. 
	ld a,b			;89fa	78 	x 
	dec b			;89fb	05 	. 
	ld b,b			;89fc	40 	@ 
	ld b,008h		;89fd	06 08 	. . 
	rlca			;89ff	07 	. 
	ret nc			;8a00	d0 	. 
	rlca			;8a01	07 	. 
	sbc a,b			;8a02	98 	. 
	ex af,af'			;8a03	08 	. 
	push iy		;8a04	fd e5 	. . 
	call 08a31h		;8a06	cd 31 8a 	. 1 . 
	cp 001h		;8a09	fe 01 	. . 
	jr nz,$+35		;8a0b	20 21 	  ! 
	call 01ffdh		;8a0d	cd fd 1f 	. . . 
	and 00fh		;8a10	e6 0f 	. . 
	cp 002h		;8a12	fe 02 	. . 
	jr nc,$+26		;8a14	30 18 	0 . 
	ld b,(iy+001h)		;8a16	fd 46 01 	. F . 
	ld c,(iy+002h)		;8a19	fd 4e 02 	. N . 
	ld ix,0722ch		;8a1c	dd 21 2c 72 	. ! , r 
	ld (ix+001h),b		;8a20	dd 70 01 	. p . 
	ld (ix+002h),c		;8a23	dd 71 02 	. q . 
	ld a,080h		;8a26	3e 80 	> . 
	ld (07273h),a		;8a28	32 73 72 	2 s r 
	call 0c9e1h		;8a2b	cd e1 c9 	. . . 
	pop iy		;8a2e	fd e1 	. . 
	ret			;8a30	c9 	. 
	push bc			;8a31	c5 	. 
	push de			;8a32	d5 	. 
	push ix		;8a33	dd e5 	. . 
	ld ix,0722ch		;8a35	dd 21 2c 72 	. ! , r 
	ld b,005h		;8a39	06 05 	. . 
	ld c,000h		;8a3b	0e 00 	. . 
	ld de,00005h		;8a3d	11 05 00 	. . . 
	bit 7,(ix+000h)		;8a40	dd cb 00 7e 	. . . ~ 
	jr z,$+3		;8a44	28 01 	( . 
	inc c			;8a46	0c 	. 
	add ix,de		;8a47	dd 19 	. . 
	djnz $-9		;8a49	10 f5 	. . 
	ld a,c			;8a4b	79 	y 
	pop ix		;8a4c	dd e1 	. . 
	pop de			;8a4e	d1 	. 
	pop bc			;8a4f	c1 	. 
	and a			;8a50	a7 	. 
	ret			;8a51	c9 	. 
	ld b,(iy+001h)		;8a52	fd 46 01 	. F . 
	ld c,(iy+002h)		;8a55	fd 4e 02 	. N . 
	ld a,c			;8a58	79 	y 
	and 00fh		;8a59	e6 0f 	. . 
	jr z,$+12		;8a5b	28 0a 	( . 
	cp 008h		;8a5d	fe 08 	. . 
	jr z,$+8		;8a5f	28 06 	( . 
	ld a,c			;8a61	79 	y 
	add a,008h		;8a62	c6 08 	. . 
	and 0f0h		;8a64	e6 f0 	. . 
	ld c,a			;8a66	4f 	O 
	call 08ad9h		;8a67	cd d9 8a 	. . . 
	ld a,(iy+001h)		;8a6a	fd 7e 01 	. ~ . 
	add a,004h		;8a6d	c6 04 	. . 
	ld (iy+001h),a		;8a6f	fd 77 01 	. w . 
	ld a,(iy+000h)		;8a72	fd 7e 00 	. ~ . 
	inc a			;8a75	3c 	< 
	ld b,a			;8a76	47 	G 
	and 007h		;8a77	e6 07 	. . 
	cp 006h		;8a79	fe 06 	. . 
	jr nc,$+5		;8a7b	30 03 	0 . 
	ld (iy+000h),b		;8a7d	fd 70 00 	. p . 
	call 08bf6h		;8a80	cd f6 8b 	. . . 
	call 08c3ah		;8a83	cd 3a 8c 	. : . 
	call 08c96h		;8a86	cd 96 8c 	. . . 
	call 08bc0h		;8a89	cd c0 8b 	. . . 
	ld a,(iy+001h)		;8a8c	fd 7e 01 	. ~ . 
	and 007h		;8a8f	e6 07 	. . 
	jr nz,$+70		;8a91	20 44 	  D 
	call 08d25h		;8a93	cd 25 8d 	. % . 
	jr nz,$+46		;8a96	20 2c 	  , 
	ld a,001h		;8a98	3e 01 	> . 
	call 08e48h		;8a9a	cd 48 8e 	. H . 
	jr nz,$+58		;8a9d	20 38 	  8 
	ld a,(iy+004h)		;8a9f	fd 7e 04 	. ~ . 
	bit 7,a		;8aa2	cb 7f 	.  
	jr nz,$+32		;8aa4	20 1e 	  . 
	bit 6,a		;8aa6	cb 77 	. w 
	jr nz,$+28		;8aa8	20 1a 	  . 
	and 00fh		;8aaa	e6 0f 	. . 
	jr nz,$+24		;8aac	20 16 	  . 
	ld a,(iy+000h)		;8aae	fd 7e 00 	. ~ . 
	and 007h		;8ab1	e6 07 	. . 
	cp 005h		;8ab3	fe 05 	. . 
	jr nc,$+15		;8ab5	30 0d 	0 . 
	ld a,080h		;8ab7	3e 80 	> . 
	ld (iy+000h),a		;8ab9	fd 77 00 	. w . 
	ld a,010h		;8abc	3e 10 	> . 
	ld (iy+004h),a		;8abe	fd 77 04 	. w . 
	xor a			;8ac1	af 	. 
	jr $+21		;8ac2	18 13 	. . 
	res 5,(iy+000h)		;8ac4	fd cb 00 ae 	. . . . 
	push iy		;8ac8	fd e5 	. . 
	call 0c9c0h		;8aca	cd c0 c9 	. . . 
	pop iy		;8acd	fd e1 	. . 
	ld a,(iy+004h)		;8acf	fd 7e 04 	. ~ . 
	add a,010h		;8ad2	c6 10 	. . 
	ld (iy+004h),a		;8ad4	fd 77 04 	. w . 
	and a			;8ad7	a7 	. 
	ret			;8ad8	c9 	. 
	ld a,b			;8ad9	78 	x 
	and 00fh		;8ada	e6 0f 	. . 
	ret nz			;8adc	c0 	. 
	call 0ac3fh		;8add	cd 3f ac 	. ? . 
	dec ix		;8ae0	dd 2b 	. + 
	dec d			;8ae2	15 	. 
	ld a,(ix+011h)		;8ae3	dd 7e 11 	. ~ . 
	and 003h		;8ae6	e6 03 	. . 
	cp 003h		;8ae8	fe 03 	. . 
	ret nz			;8aea	c0 	. 
	bit 3,c		;8aeb	cb 59 	. Y 
	jr nz,$+10		;8aed	20 08 	  . 
	ld a,(ix+010h)		;8aef	dd 7e 10 	. ~ . 
	and 003h		;8af2	e6 03 	. . 
	cp 003h		;8af4	fe 03 	. . 
	ret nz			;8af6	c0 	. 
	ld a,(ix+001h)		;8af7	dd 7e 01 	. ~ . 
	and 00ch		;8afa	e6 0c 	. . 
	cp 00ch		;8afc	fe 0c 	. . 
	jr nz,$+11		;8afe	20 09 	  . 
	ld a,b			;8b00	78 	x 
	cp 0e8h		;8b01	fe e8 	. . 
	jr nc,$+6		;8b03	30 04 	0 . 
	set 5,(ix+001h)		;8b05	dd cb 01 ee 	. . . . 
	bit 0,(ix+001h)		;8b09	dd cb 01 46 	. . . F 
	jr z,$+16		;8b0d	28 0e 	( . 
	bit 1,(ix+000h)		;8b0f	dd cb 00 4e 	. . . N 
	jr z,$+10		;8b13	28 08 	( . 
	bit 3,c		;8b15	cb 59 	. Y 
	jr nz,$+6		;8b17	20 04 	  . 
	set 7,(ix+001h)		;8b19	dd cb 01 fe 	. . . . 
	ld a,d			;8b1d	7a 	z 
	inc a			;8b1e	3c 	< 
	call 08bb1h		;8b1f	cd b1 8b 	. . . 
	ld a,b			;8b22	78 	x 
	cp 0b8h		;8b23	fe b8 	. . 
	jr nc,$+47		;8b25	30 2d 	0 - 
	ld a,(ix+001h)		;8b27	dd 7e 01 	. ~ . 
	and 00ch		;8b2a	e6 0c 	. . 
	cp 00ch		;8b2c	fe 0c 	. . 
	jr nz,$+6		;8b2e	20 04 	  . 
	set 4,(ix+011h)		;8b30	dd cb 11 e6 	. . . . 
	ld a,(ix+011h)		;8b34	dd 7e 11 	. ~ . 
	and 005h		;8b37	e6 05 	. . 
	cp 005h		;8b39	fe 05 	. . 
	jr nz,$+19		;8b3b	20 11 	  . 
	ld a,(ix+010h)		;8b3d	dd 7e 10 	. ~ . 
	and 00ah		;8b40	e6 0a 	. . 
	cp 00ah		;8b42	fe 0a 	. . 
	jr nz,$+10		;8b44	20 08 	  . 
	bit 3,c		;8b46	cb 59 	. Y 
	jr nz,$+6		;8b48	20 04 	  . 
	set 7,(ix+011h)		;8b4a	dd cb 11 fe 	. . . . 
	ld a,d			;8b4e	7a 	z 
	add a,011h		;8b4f	c6 11 	. . 
	call 08bb1h		;8b51	cd b1 8b 	. . . 
	bit 3,c		;8b54	cb 59 	. Y 
	ret nz			;8b56	c0 	. 
	ld a,(ix+000h)		;8b57	dd 7e 00 	. ~ . 
	and 00ch		;8b5a	e6 0c 	. . 
	cp 00ch		;8b5c	fe 0c 	. . 
	jr nz,$+11		;8b5e	20 09 	  . 
	ld a,b			;8b60	78 	x 
	cp 0b8h		;8b61	fe b8 	. . 
	jr nc,$+6		;8b63	30 04 	0 . 
	set 5,(ix+000h)		;8b65	dd cb 00 ee 	. . . . 
	ld a,(ix+000h)		;8b69	dd 7e 00 	. ~ . 
	and 00ah		;8b6c	e6 0a 	. . 
	cp 00ah		;8b6e	fe 0a 	. . 
	jr nz,$+15		;8b70	20 0d 	  . 
	ld a,(ix+001h)		;8b72	dd 7e 01 	. ~ . 
	and 005h		;8b75	e6 05 	. . 
	cp 005h		;8b77	fe 05 	. . 
	jr nz,$+6		;8b79	20 04 	  . 
	set 6,(ix+000h)		;8b7b	dd cb 00 f6 	. . . . 
	ld a,d			;8b7f	7a 	z 
	call 08bb1h		;8b80	cd b1 8b 	. . . 
	ld a,b			;8b83	78 	x 
	cp 0b8h		;8b84	fe b8 	. . 
	ret nc			;8b86	d0 	. 
	ld a,(ix+000h)		;8b87	dd 7e 00 	. ~ . 
	and 00ch		;8b8a	e6 0c 	. . 
	cp 00ch		;8b8c	fe 0c 	. . 
	jr nz,$+6		;8b8e	20 04 	  . 
	set 4,(ix+010h)		;8b90	dd cb 10 e6 	. . . . 
	ld a,(ix+010h)		;8b94	dd 7e 10 	. ~ . 
	and 00ah		;8b97	e6 0a 	. . 
	cp 00ah		;8b99	fe 0a 	. . 
	jr nz,$+15		;8b9b	20 0d 	  . 
	ld a,(ix+011h)		;8b9d	dd 7e 11 	. ~ . 
	and 005h		;8ba0	e6 05 	. . 
	cp 005h		;8ba2	fe 05 	. . 
	jr nz,$+6		;8ba4	20 04 	  . 
	set 6,(ix+010h)		;8ba6	dd cb 10 f6 	. . . . 
	ld a,d			;8baa	7a 	z 
	add a,010h		;8bab	c6 10 	. . 
	call 08bb1h		;8bad	cd b1 8b 	. . . 
	ret			;8bb0	c9 	. 
	push bc			;8bb1	c5 	. 
	push de			;8bb2	d5 	. 
	push ix		;8bb3	dd e5 	. . 
	ld hl,07259h		;8bb5	21 59 72 	! Y r 
	call 0abe1h		;8bb8	cd e1 ab 	. . . 
	pop ix		;8bbb	dd e1 	. . 
	pop de			;8bbd	d1 	. 
	pop bc			;8bbe	c1 	. 
	ret			;8bbf	c9 	. 
	ld a,(07284h)		;8bc0	3a 84 72 	: . r 
	ld d,a			;8bc3	57 	W 
	bit 7,(iy+004h)		;8bc4	fd cb 04 7e 	. . . ~ 
	jr z,$+6		;8bc8	28 04 	( . 
	add a,004h		;8bca	c6 04 	. . 
	jr $+24		;8bcc	18 16 	. . 
	ld a,(07285h)		;8bce	3a 85 72 	: . r 
	ld e,a			;8bd1	5f 	_ 
	call 08cfeh		;8bd2	cd fe 8c 	. . . 
	jr nz,$+31		;8bd5	20 1d 	  . 
	set 7,(iy+004h)		;8bd7	fd cb 04 fe 	. . . . 
	ld a,(0726eh)		;8bdb	3a 6e 72 	: n r 
	set 6,a		;8bde	cb f7 	. . 
	ld (0726eh),a		;8be0	32 6e 72 	2 n r 
	ld a,d			;8be3	7a 	z 
	ld (07284h),a		;8be4	32 84 72 	2 . r 
	xor a			;8be7	af 	. 
	ld (07286h),a		;8be8	32 86 72 	2 . r 
	ld a,(07281h)		;8beb	3a 81 72 	: . r 
	set 7,a		;8bee	cb ff 	. . 
	ld (07281h),a		;8bf0	32 81 72 	2 . r 
	xor a			;8bf3	af 	. 
	and a			;8bf4	a7 	. 
	ret			;8bf5	c9 	. 
	ld a,(072bah)		;8bf6	3a ba 72 	: . r 
	ld b,a			;8bf9	47 	G 
	ld a,001h		;8bfa	3e 01 	> . 
	bit 7,b		;8bfc	cb 78 	. x 
	jr z,$+58		;8bfe	28 38 	( 8 
	ld a,(072bfh)		;8c00	3a bf 72 	: . r 
	ld d,a			;8c03	57 	W 
	bit 6,(iy+004h)		;8c04	fd cb 04 76 	. . . v 
	jr z,$+7		;8c08	28 05 	( . 
	add a,004h		;8c0a	c6 04 	. . 
	ld d,a			;8c0c	57 	W 
	jr $+27		;8c0d	18 19 	. . 
	ld a,(072beh)		;8c0f	3a be 72 	: . r 
	ld e,a			;8c12	5f 	_ 
	call 08cfeh		;8c13	cd fe 8c 	. . . 
	jr nz,$+34		;8c16	20 20 	    
	ld a,(072bdh)		;8c18	3a bd 72 	: . r 
	set 7,a		;8c1b	cb ff 	. . 
	ld (072bdh),a		;8c1d	32 bd 72 	2 . r 
	set 6,(iy+004h)		;8c20	fd cb 04 f6 	. . . . 
	inc (iy+004h)		;8c24	fd 34 04 	. 4 . 
	ld a,d			;8c27	7a 	z 
	ld (072bfh),a		;8c28	32 bf 72 	2 . r 
	ld b,d			;8c2b	42 	B 
	ld a,(072beh)		;8c2c	3a be 72 	: . r 
	ld c,a			;8c2f	4f 	O 
	ld d,00bh		;8c30	16 0b 	. . 
	ld a,003h		;8c32	3e 03 	> . 
	call 0b629h		;8c34	cd 29 b6 	. ) . 
	xor a			;8c37	af 	. 
	and a			;8c38	a7 	. 
	ret			;8c39	c9 	. 
	ld b,007h		;8c3a	06 07 	. . 
	ld ix,0728eh		;8c3c	dd 21 8e 72 	. ! . r 
	push bc			;8c40	c5 	. 
	bit 7,(ix+004h)		;8c41	dd cb 04 7e 	. . . ~ 
	jr z,$+72		;8c45	28 46 	( F 
	bit 6,(ix+004h)		;8c47	dd cb 04 76 	. . . v 
	jr nz,$+66		;8c4b	20 40 	  @ 
	ld d,(ix+002h)		;8c4d	dd 56 02 	. V . 
	ld e,(ix+001h)		;8c50	dd 5e 01 	. ^ . 
	bit 7,(ix+000h)		;8c53	dd cb 00 7e 	. . . ~ 
	jr z,$+17		;8c57	28 0f 	( . 
	ld b,(ix+005h)		;8c59	dd 46 05 	. F . 
	ld a,(0722ah)		;8c5c	3a 2a 72 	: * r 
	cp b			;8c5f	b8 	. 
	jr nz,$+45		;8c60	20 2b 	  + 
	ld a,d			;8c62	7a 	z 
	add a,004h		;8c63	c6 04 	. . 
	ld d,a			;8c65	57 	W 
	jr $+20		;8c66	18 12 	. . 
	call 08cfeh		;8c68	cd fe 8c 	. . . 
	jr nz,$+34		;8c6b	20 20 	    
	set 7,(ix+000h)		;8c6d	dd cb 00 fe 	. . . . 
	ld a,(0722ah)		;8c71	3a 2a 72 	: * r 
	ld (ix+005h),a		;8c74	dd 77 05 	. w . 
	inc (iy+004h)		;8c77	fd 34 04 	. 4 . 
	ld (ix+002h),d		;8c7a	dd 72 02 	. r . 
	ld b,d			;8c7d	42 	B 
	ld c,e			;8c7e	4b 	K 
	call 0b7efh		;8c7f	cd ef b7 	. . . 
	add a,005h		;8c82	c6 05 	. . 
	ld d,025h		;8c84	16 25 	. % 
	push ix		;8c86	dd e5 	. . 
	call 0b629h		;8c88	cd 29 b6 	. ) . 
	pop ix		;8c8b	dd e1 	. . 
	ld de,00006h		;8c8d	11 06 00 	. . . 
	add ix,de		;8c90	dd 19 	. . 
	pop bc			;8c92	c1 	. 
	djnz $-83		;8c93	10 ab 	. . 
	ret			;8c95	c9 	. 
	ld b,003h		;8c96	06 03 	. . 
	ld ix,072c7h		;8c98	dd 21 c7 72 	. ! . r 
	push bc			;8c9c	c5 	. 
	bit 7,(ix+004h)		;8c9d	dd cb 04 7e 	. . . ~ 
	jr z,$+84		;8ca1	28 52 	( R 
	ld d,(ix+002h)		;8ca3	dd 56 02 	. V . 
	ld e,(ix+001h)		;8ca6	dd 5e 01 	. ^ . 
	bit 7,(ix+000h)		;8ca9	dd cb 00 7e 	. . . ~ 
	jr z,$+17		;8cad	28 0f 	( . 
	ld b,(ix+005h)		;8caf	dd 46 05 	. F . 
	ld a,(0722ah)		;8cb2	3a 2a 72 	: * r 
	cp b			;8cb5	b8 	. 
	jr nz,$+63		;8cb6	20 3d 	  = 
	ld a,d			;8cb8	7a 	z 
	add a,004h		;8cb9	c6 04 	. . 
	ld d,a			;8cbb	57 	W 
	jr $+20		;8cbc	18 12 	. . 
	call 08cfeh		;8cbe	cd fe 8c 	. . . 
	jr nz,$+52		;8cc1	20 32 	  2 
	set 7,(ix+000h)		;8cc3	dd cb 00 fe 	. . . . 
	ld a,(0722ah)		;8cc7	3a 2a 72 	: * r 
	ld (ix+005h),a		;8cca	dd 77 05 	. w . 
	inc (iy+004h)		;8ccd	fd 34 04 	. 4 . 
	ld (ix+002h),d		;8cd0	dd 72 02 	. r . 
	ld b,d			;8cd3	42 	B 
	ld c,e			;8cd4	4b 	K 
	push ix		;8cd5	dd e5 	. . 
	pop hl			;8cd7	e1 	. 
	xor a			;8cd8	af 	. 
	ld de,072c7h		;8cd9	11 c7 72 	. . r 
	and a			;8cdc	a7 	. 
	sbc hl,de		;8cdd	ed 52 	. R 
	jr z,$+11		;8cdf	28 09 	( . 
	ld de,00006h		;8ce1	11 06 00 	. . . 
	inc a			;8ce4	3c 	< 
	and a			;8ce5	a7 	. 
	sbc hl,de		;8ce6	ed 52 	. R 
	jr nz,$-4		;8ce8	20 fa 	  . 
	add a,011h		;8cea	c6 11 	. . 
	ld d,005h		;8cec	16 05 	. . 
	push ix		;8cee	dd e5 	. . 
	call 0b629h		;8cf0	cd 29 b6 	. ) . 
	pop ix		;8cf3	dd e1 	. . 
	ld de,00006h		;8cf5	11 06 00 	. . . 
	add ix,de		;8cf8	dd 19 	. . 
	pop bc			;8cfa	c1 	. 
	djnz $-95		;8cfb	10 9f 	. . 
	ret			;8cfd	c9 	. 
	push bc			;8cfe	c5 	. 
	ld c,001h		;8cff	0e 01 	. . 
	ld a,(iy+001h)		;8d01	fd 7e 01 	. ~ . 
	sub d			;8d04	92 	. 
	jr nc,$+4		;8d05	30 02 	0 . 
	cpl			;8d07	2f 	/ 
	inc a			;8d08	3c 	< 
	cp 008h		;8d09	fe 08 	. . 
	jr nc,$+22		;8d0b	30 14 	0 . 
	ld a,(iy+002h)		;8d0d	fd 7e 02 	. ~ . 
	sub e			;8d10	93 	. 
	jr nc,$+4		;8d11	30 02 	0 . 
	cpl			;8d13	2f 	/ 
	inc a			;8d14	3c 	< 
	cp 009h		;8d15	fe 09 	. . 
	jr nc,$+10		;8d17	30 08 	0 . 
	ld a,(iy+001h)		;8d19	fd 7e 01 	. ~ . 
	add a,004h		;8d1c	c6 04 	. . 
	ld d,a			;8d1e	57 	W 
	ld c,000h		;8d1f	0e 00 	. . 
	ld a,c			;8d21	79 	y 
	pop bc			;8d22	c1 	. 
	or a			;8d23	b7 	. 
	ret			;8d24	c9 	. 
	ld ix,0722ch		;8d25	dd 21 2c 72 	. ! , r 
	ld bc,00000h		;8d29	01 00 00 	. . . 
	ld a,(0722ah)		;8d2c	3a 2a 72 	: * r 
	cp c			;8d2f	b9 	. 
	jr z,$+80		;8d30	28 4e 	( N 
	ld a,(ix+000h)		;8d32	dd 7e 00 	. ~ . 
	bit 7,a		;8d35	cb 7f 	.  
	jr z,$+73		;8d37	28 47 	( G 
	bit 6,a		;8d39	cb 77 	. w 
	jr nz,$+69		;8d3b	20 43 	  C 
	ld a,(iy+002h)		;8d3d	fd 7e 02 	. ~ . 
	sub (ix+002h)		;8d40	dd 96 02 	. . . 
	jr nc,$+4		;8d43	30 02 	0 . 
	cpl			;8d45	2f 	/ 
	inc a			;8d46	3c 	< 
	cp 010h		;8d47	fe 10 	. . 
	jr nc,$+55		;8d49	30 35 	0 5 
	ld a,(ix+001h)		;8d4b	dd 7e 01 	. ~ . 
	sub (iy+001h)		;8d4e	fd 96 01 	. . . 
	jr c,$+47		;8d51	38 2d 	8 - 
	cp 009h		;8d53	fe 09 	. . 
	jr nc,$+43		;8d55	30 29 	0 ) 
	res 6,(ix+000h)		;8d57	dd cb 00 b6 	. . . . 
	res 5,(ix+000h)		;8d5b	dd cb 00 ae 	. . . . 
	ld a,(iy+004h)		;8d5f	fd 7e 04 	. ~ . 
	and 0cfh		;8d62	e6 cf 	. . 
	or 020h		;8d64	f6 20 	.   
	ld (ix+004h),a		;8d66	dd 77 04 	. w . 
	bit 3,(ix+000h)		;8d69	dd cb 00 5e 	. . . ^ 
	jr nz,$+18		;8d6d	20 10 	  . 
	set 3,(ix+000h)		;8d6f	dd cb 00 de 	. . . . 
	ld hl,0000fh		;8d73	21 0f 00 	! . . 
	xor a			;8d76	af 	. 
	push bc			;8d77	c5 	. 
	call 01fcdh		;8d78	cd cd 1f 	. . . 
	pop bc			;8d7b	c1 	. 
	ld (ix+003h),a		;8d7c	dd 77 03 	. w . 
	inc b			;8d7f	04 	. 
	ld de,00005h		;8d80	11 05 00 	. . . 
	add ix,de		;8d83	dd 19 	. . 
	inc c			;8d85	0c 	. 
	ld a,c			;8d86	79 	y 
	cp 005h		;8d87	fe 05 	. . 
	jr c,$-93		;8d89	38 a1 	8 . 
	ld a,b			;8d8b	78 	x 
	and a			;8d8c	a7 	. 
	ret			;8d8d	c9 	. 
	bit 6,(iy+004h)		;8d8e	fd cb 04 76 	. . . v 
	jr z,$+9		;8d92	28 07 	( . 
	call 0b76dh		;8d94	cd 6d b7 	. m . 
	ld l,003h		;8d97	2e 03 	. . 
	jr nz,$+108		;8d99	20 6a 	  j 
	ld ix,0728eh		;8d9b	dd 21 8e 72 	. ! . r 
	ld b,007h		;8d9f	06 07 	. . 
	push bc			;8da1	c5 	. 
	ld a,(ix+004h)		;8da2	dd 7e 04 	. ~ . 
	bit 7,a		;8da5	cb 7f 	.  
	jr z,$+30		;8da7	28 1c 	( . 
	bit 6,a		;8da9	cb 77 	. w 
	jr nz,$+26		;8dab	20 18 	  . 
	bit 7,(ix+000h)		;8dad	dd cb 00 7e 	. . . ~ 
	jr z,$+20		;8db1	28 12 	( . 
	ld b,(ix+005h)		;8db3	dd 46 05 	. F . 
	ld a,(0722ah)		;8db6	3a 2a 72 	: * r 
	cp b			;8db9	b8 	. 
	jr nz,$+11		;8dba	20 09 	  . 
	call 0b7c4h		;8dbc	cd c4 b7 	. . . 
	pop bc			;8dbf	c1 	. 
	ld l,002h		;8dc0	2e 02 	. . 
	jr z,$+67		;8dc2	28 41 	( A 
	push bc			;8dc4	c5 	. 
	ld de,00006h		;8dc5	11 06 00 	. . . 
	add ix,de		;8dc8	dd 19 	. . 
	pop bc			;8dca	c1 	. 
	djnz $-42		;8dcb	10 d4 	. . 
	ld ix,072c7h		;8dcd	dd 21 c7 72 	. ! . r 
	ld b,003h		;8dd1	06 03 	. . 
	push bc			;8dd3	c5 	. 
	bit 7,(ix+004h)		;8dd4	dd cb 04 7e 	. . . ~ 
	jr z,$+20		;8dd8	28 12 	( . 
	bit 7,(ix+000h)		;8dda	dd cb 00 7e 	. . . ~ 
	jr z,$+14		;8dde	28 0c 	( . 
	ld b,(ix+005h)		;8de0	dd 46 05 	. F . 
	ld a,(0722ah)		;8de3	3a 2a 72 	: * r 
	cp b			;8de6	b8 	. 
	jr nz,$+5		;8de7	20 03 	  . 
	call 0b832h		;8de9	cd 32 b8 	. 2 . 
	pop bc			;8dec	c1 	. 
	ld de,00006h		;8ded	11 06 00 	. . . 
	add ix,de		;8df0	dd 19 	. . 
	djnz $-31		;8df2	10 df 	. . 
	ld l,000h		;8df4	2e 00 	. . 
	bit 7,(iy+004h)		;8df6	fd cb 04 7e 	. . . ~ 
	jr z,$+11		;8dfa	28 09 	( . 
	push iy		;8dfc	fd e5 	. . 
	call 0ca17h		;8dfe	cd 17 ca 	. . . 
	pop iy		;8e01	fd e1 	. . 
	ld l,001h		;8e03	2e 01 	. . 
	res 7,(iy+000h)		;8e05	fd cb 00 be 	. . . . 
	res 3,(iy+000h)		;8e09	fd cb 00 9e 	. . . . 
	ld a,l			;8e0d	7d 	} 
	and a			;8e0e	a7 	. 
	ret			;8e0f	c9 	. 
	call 08e48h		;8e10	cd 48 8e 	. H . 
	jr z,$+51		;8e13	28 31 	( 1 
	ld e,a			;8e15	5f 	_ 
	ld a,(07284h)		;8e16	3a 84 72 	: . r 
	sub (iy+001h)		;8e19	fd 96 01 	. . . 
	jr c,$+22		;8e1c	38 14 	8 . 
	cp 011h		;8e1e	fe 11 	. . 
	jr nc,$+18		;8e20	30 10 	0 . 
	ld a,(07285h)		;8e22	3a 85 72 	: . r 
	sub (iy+002h)		;8e25	fd 96 02 	. . . 
	jr nc,$+4		;8e28	30 02 	0 . 
	cpl			;8e2a	2f 	/ 
	inc a			;8e2b	3c 	< 
	ld d,000h		;8e2c	16 00 	. . 
	cp 008h		;8e2e	fe 08 	. . 
	jr c,$+21		;8e30	38 13 	8 . 
	ld b,0c8h		;8e32	06 c8 	. . 
	dec e			;8e34	1d 	. 
	jr z,$+6		;8e35	28 04 	( . 
	res 6,b		;8e37	cb b0 	. . 
	set 5,b		;8e39	cb e8 	. . 
	ld (iy+000h),b		;8e3b	fd 70 00 	. p . 
	ld a,010h		;8e3e	3e 10 	> . 
	ld (iy+004h),a		;8e40	fd 77 04 	. w . 
	ld d,001h		;8e43	16 01 	. . 
	ld a,d			;8e45	7a 	z 
	and a			;8e46	a7 	. 
	ret			;8e47	c9 	. 
	ld d,a			;8e48	57 	W 
	ld b,(iy+001h)		;8e49	fd 46 01 	. F . 
	ld c,(iy+002h)		;8e4c	fd 4e 02 	. N . 
	push de			;8e4f	d5 	. 
	call 0ac3fh		;8e50	cd 3f ac 	. ? . 
	pop de			;8e53	d1 	. 
	ld a,b			;8e54	78 	x 
	cp 0b0h		;8e55	fe b0 	. . 
	jr nc,$+31		;8e57	30 1d 	0 . 
	ld a,(iy+002h)		;8e59	fd 7e 02 	. ~ . 
	rlca			;8e5c	07 	. 
	rlca			;8e5d	07 	. 
	rlca			;8e5e	07 	. 
	rlca			;8e5f	07 	. 
	and 0f0h		;8e60	e6 f0 	. . 
	ld c,a			;8e62	4f 	O 
	ld a,(iy+001h)		;8e63	fd 7e 01 	. ~ . 
	and 00fh		;8e66	e6 0f 	. . 
	or c			;8e68	b1 	. 
	ld b,008h		;8e69	06 08 	. . 
	ld hl,08f98h		;8e6b	21 98 8f 	! . . 
	cp (hl)			;8e6e	be 	. 
	jr z,$+11		;8e6f	28 09 	( . 
	inc hl			;8e71	23 	# 
	inc hl			;8e72	23 	# 
	inc hl			;8e73	23 	# 
	djnz $-6		;8e74	10 f8 	. . 
	xor a			;8e76	af 	. 
	jp 08f96h		;8e77	c3 96 8f 	. . . 
	inc hl			;8e7a	23 	# 
	push de			;8e7b	d5 	. 
	ld e,(hl)			;8e7c	5e 	^ 
	inc hl			;8e7d	23 	# 
	ld d,(hl)			;8e7e	56 	V 
	push ix		;8e7f	dd e5 	. . 
	push de			;8e81	d5 	. 
	pop ix		;8e82	dd e1 	. . 
	pop hl			;8e84	e1 	. 
	pop de			;8e85	d1 	. 
	jp (ix)		;8e86	dd e9 	. . 
	ld bc,00010h		;8e88	01 10 00 	. . . 
	add hl,bc			;8e8b	09 	. 
	xor a			;8e8c	af 	. 
	bit 0,(hl)		;8e8d	cb 46 	. F 
	jr z,$+8		;8e8f	28 06 	( . 
	dec hl			;8e91	2b 	+ 
	bit 1,(hl)		;8e92	cb 4e 	. N 
	jr z,$+3		;8e94	28 01 	( . 
	inc a			;8e96	3c 	< 
	jp 08f96h		;8e97	c3 96 8f 	. . . 
	ld bc,00010h		;8e9a	01 10 00 	. . . 
	add hl,bc			;8e9d	09 	. 
	xor a			;8e9e	af 	. 
	bit 0,(hl)		;8e9f	cb 46 	. F 
	jr z,$+43		;8ea1	28 29 	( ) 
	ld a,d			;8ea3	7a 	z 
	and a			;8ea4	a7 	. 
	jr nz,$+15		;8ea5	20 0d 	  . 
	bit 1,(hl)		;8ea7	cb 4e 	. N 
	jr z,$+35		;8ea9	28 21 	( ! 
	dec hl			;8eab	2b 	+ 
	bit 1,(hl)		;8eac	cb 4e 	. N 
	jr z,$+30		;8eae	28 1c 	( . 
	ld a,001h		;8eb0	3e 01 	> . 
	jr $+26		;8eb2	18 18 	. . 
	ld b,0fch		;8eb4	06 fc 	. . 
	bit 1,(hl)		;8eb6	cb 4e 	. N 
	jr z,$+11		;8eb8	28 09 	( . 
	ld b,004h		;8eba	06 04 	. . 
	dec hl			;8ebc	2b 	+ 
	bit 1,(hl)		;8ebd	cb 4e 	. N 
	jr z,$+4		;8ebf	28 02 	( . 
	ld b,000h		;8ec1	06 00 	. . 
	ld a,(iy+002h)		;8ec3	fd 7e 02 	. ~ . 
	add a,b			;8ec6	80 	. 
	ld (iy+002h),a		;8ec7	fd 77 02 	. w . 
	ld a,002h		;8eca	3e 02 	> . 
	jp 08f96h		;8ecc	c3 96 8f 	. . . 
	ld a,002h		;8ecf	3e 02 	> . 
	bit 5,(hl)		;8ed1	cb 6e 	. n 
	jr nz,$+16		;8ed3	20 0e 	  . 
	ld bc,00010h		;8ed5	01 10 00 	. . . 
	add hl,bc			;8ed8	09 	. 
	xor a			;8ed9	af 	. 
	bit 0,(hl)		;8eda	cb 46 	. F 
	jr z,$+7		;8edc	28 05 	( . 
	bit 1,(hl)		;8ede	cb 4e 	. N 
	jr z,$+3		;8ee0	28 01 	( . 
	inc a			;8ee2	3c 	< 
	jp 08f96h		;8ee3	c3 96 8f 	. . . 
	ld bc,00010h		;8ee6	01 10 00 	. . . 
	add hl,bc			;8ee9	09 	. 
	xor a			;8eea	af 	. 
	bit 1,(hl)		;8eeb	cb 4e 	. N 
	jr z,$+43		;8eed	28 29 	( ) 
	ld a,d			;8eef	7a 	z 
	and a			;8ef0	a7 	. 
	jr nz,$+15		;8ef1	20 0d 	  . 
	bit 0,(hl)		;8ef3	cb 46 	. F 
	jr z,$+35		;8ef5	28 21 	( ! 
	inc hl			;8ef7	23 	# 
	bit 0,(hl)		;8ef8	cb 46 	. F 
	jr z,$+30		;8efa	28 1c 	( . 
	ld a,001h		;8efc	3e 01 	> . 
	jr $+26		;8efe	18 18 	. . 
	ld b,004h		;8f00	06 04 	. . 
	bit 0,(hl)		;8f02	cb 46 	. F 
	jr z,$+11		;8f04	28 09 	( . 
	ld b,0fch		;8f06	06 fc 	. . 
	inc hl			;8f08	23 	# 
	bit 0,(hl)		;8f09	cb 46 	. F 
	jr z,$+4		;8f0b	28 02 	( . 
	ld b,000h		;8f0d	06 00 	. . 
	ld a,(iy+002h)		;8f0f	fd 7e 02 	. ~ . 
	add a,b			;8f12	80 	. 
	ld (iy+002h),a		;8f13	fd 77 02 	. w . 
	ld a,002h		;8f16	3e 02 	> . 
	jp 08f96h		;8f18	c3 96 8f 	. . . 
	xor a			;8f1b	af 	. 
	bit 2,(hl)		;8f1c	cb 56 	. V 
	jr z,$+9		;8f1e	28 07 	( . 
	dec hl			;8f20	2b 	+ 
	bit 3,(hl)		;8f21	cb 5e 	. ^ 
	jr z,$+4		;8f23	28 02 	( . 
	ld a,002h		;8f25	3e 02 	> . 
	jp 08f96h		;8f27	c3 96 8f 	. . . 
	xor a			;8f2a	af 	. 
	bit 2,(hl)		;8f2b	cb 56 	. V 
	jr z,$+42		;8f2d	28 28 	( ( 
	ld a,d			;8f2f	7a 	z 
	and a			;8f30	a7 	. 
	jr nz,$+15		;8f31	20 0d 	  . 
	bit 3,(hl)		;8f33	cb 5e 	. ^ 
	jr z,$+34		;8f35	28 20 	(   
	dec hl			;8f37	2b 	+ 
	bit 3,(hl)		;8f38	cb 5e 	. ^ 
	jr z,$+29		;8f3a	28 1b 	( . 
	ld a,002h		;8f3c	3e 02 	> . 
	jr $+25		;8f3e	18 17 	. . 
	ld b,0fch		;8f40	06 fc 	. . 
	bit 3,(hl)		;8f42	cb 5e 	. ^ 
	jr z,$+10		;8f44	28 08 	( . 
	ld b,004h		;8f46	06 04 	. . 
	bit 3,(hl)		;8f48	cb 5e 	. ^ 
	jr z,$+4		;8f4a	28 02 	( . 
	ld b,000h		;8f4c	06 00 	. . 
	ld a,(iy+002h)		;8f4e	fd 7e 02 	. ~ . 
	add a,b			;8f51	80 	. 
	ld (iy+002h),a		;8f52	fd 77 02 	. w . 
	ld a,002h		;8f55	3e 02 	> . 
	jp 08f96h		;8f57	c3 96 8f 	. . . 
	xor a			;8f5a	af 	. 
	bit 2,(hl)		;8f5b	cb 56 	. V 
	jr z,$+8		;8f5d	28 06 	( . 
	bit 3,(hl)		;8f5f	cb 5e 	. ^ 
	jr z,$+4		;8f61	28 02 	( . 
	ld a,002h		;8f63	3e 02 	> . 
	jp 08f96h		;8f65	c3 96 8f 	. . . 
	xor a			;8f68	af 	. 
	bit 3,(hl)		;8f69	cb 5e 	. ^ 
	jr z,$+43		;8f6b	28 29 	( ) 
	ld a,d			;8f6d	7a 	z 
	and a			;8f6e	a7 	. 
	jr nz,$+15		;8f6f	20 0d 	  . 
	bit 2,(hl)		;8f71	cb 56 	. V 
	jr z,$+35		;8f73	28 21 	( ! 
	inc hl			;8f75	23 	# 
	bit 2,(hl)		;8f76	cb 56 	. V 
	jr z,$+30		;8f78	28 1c 	( . 
	ld a,002h		;8f7a	3e 02 	> . 
	jr $+26		;8f7c	18 18 	. . 
	ld b,004h		;8f7e	06 04 	. . 
	bit 2,(hl)		;8f80	cb 56 	. V 
	jr z,$+11		;8f82	28 09 	( . 
	ld b,0fch		;8f84	06 fc 	. . 
	inc hl			;8f86	23 	# 
	bit 2,(hl)		;8f87	cb 56 	. V 
	jr z,$+4		;8f89	28 02 	( . 
	ld b,000h		;8f8b	06 00 	. . 
	ld a,(iy+002h)		;8f8d	fd 7e 02 	. ~ . 
	add a,b			;8f90	80 	. 
	ld (iy+002h),a		;8f91	fd 77 02 	. w . 
	ld a,002h		;8f94	3e 02 	> . 
	and a			;8f96	a7 	. 
	ret			;8f97	c9 	. 
	nop			;8f98	00 	. 
	adc a,b			;8f99	88 	. 
	adc a,(hl)			;8f9a	8e 	. 
	ld b,b			;8f9b	40 	@ 
	sbc a,d			;8f9c	9a 	. 
	adc a,(hl)			;8f9d	8e 	. 
	add a,b			;8f9e	80 	. 
	rst 8			;8f9f	cf 	. 
	adc a,(hl)			;8fa0	8e 	. 
	ret nz			;8fa1	c0 	. 
	and 08eh		;8fa2	e6 8e 	. . 
	ex af,af'			;8fa4	08 	. 
	dec de			;8fa5	1b 	. 
	adc a,a			;8fa6	8f 	. 
	ld c,b			;8fa7	48 	H 
	ld hl,(0888fh)		;8fa8	2a 8f 88 	* . . 
	ld e,d			;8fab	5a 	Z 
	adc a,a			;8fac	8f 	. 
	ret z			;8fad	c8 	. 
	ld l,b			;8fae	68 	h 
	adc a,a			;8faf	8f 	. 
	call 08fc4h		;8fb0	cd c4 8f 	. . . 
	jr nz,$+15		;8fb3	20 0d 	  . 
	ld a,(iy+000h)		;8fb5	fd 7e 00 	. ~ . 
	and 0f8h		;8fb8	e6 f8 	. . 
	res 6,a		;8fba	cb b7 	. . 
	set 5,a		;8fbc	cb ef 	. . 
	ld (iy+000h),a		;8fbe	fd 77 00 	. w . 
	xor a			;8fc1	af 	. 
	and a			;8fc2	a7 	. 
	ret			;8fc3	c9 	. 
	ld a,(iy+000h)		;8fc4	fd 7e 00 	. ~ . 
	inc a			;8fc7	3c 	< 
	ld (iy+000h),a		;8fc8	fd 77 00 	. w . 
	and 003h		;8fcb	e6 03 	. . 
	cp 003h		;8fcd	fe 03 	. . 
	ret			;8fcf	c9 	. 
	nop			;8fd0	00 	. 
	ld iy,072d9h		;8fd1	fd 21 d9 72 	. ! . r 
	ld a,(iy+000h)		;8fd5	fd 7e 00 	. ~ . 
	bit 7,(iy+000h)		;8fd8	fd cb 00 7e 	. . . ~ 
	jr z,$+21		;8fdc	28 13 	( . 
	and 07fh		;8fde	e6 7f 	.  
	or 040h		;8fe0	f6 40 	. @ 
	ld (iy+000h),a		;8fe2	fd 77 00 	. w . 
	inc (iy+004h)		;8fe5	fd 34 04 	. 4 . 
	push iy		;8fe8	fd e5 	. . 
	call 0c993h		;8fea	cd 93 c9 	. . . 
	pop iy		;8fed	fd e1 	. . 
	jr $+22		;8fef	18 14 	. . 
	and 078h		;8ff1	e6 78 	. x 
	jr z,$+126		;8ff3	28 7c 	( | 
	ld a,(iy+003h)		;8ff5	fd 7e 03 	. ~ . 
	call 01fd0h		;8ff8	cd d0 1f 	. . . 
	and a			;8ffb	a7 	. 
	jr z,$+117		;8ffc	28 73 	( s 
	ld a,(iy+000h)		;8ffe	fd 7e 00 	. ~ . 
	bit 6,a		;9001	cb 77 	. w 
	jr z,$+85		;9003	28 53 	( S 
	call 09074h		;9005	cd 74 90 	. t . 
	call 09099h		;9008	cd 99 90 	. . . 
	bit 2,e		;900b	cb 53 	. S 
	jr nz,$+54		;900d	20 34 	  4 
	call 0912dh		;900f	cd 2d 91 	. - . 
	call 092f2h		;9012	cd f2 92 	. . . 
	cp 002h		;9015	fe 02 	. . 
	jr z,$+92		;9017	28 5a 	( Z 
	cp 001h		;9019	fe 01 	. . 
	jr z,$+40		;901b	28 26 	( & 
	call 0936fh		;901d	cd 6f 93 	. o . 
	cp 002h		;9020	fe 02 	. . 
	jr nz,$+6		;9022	20 04 	  . 
	ld a,003h		;9024	3e 03 	> . 
	jr $+77		;9026	18 4b 	. K 
	cp 001h		;9028	fe 01 	. . 
	jr z,$+25		;902a	28 17 	( . 
	call 09337h		;902c	cd 37 93 	. 7 . 
	and a			;902f	a7 	. 
	jr nz,$+19		;9030	20 11 	  . 
	call 09399h		;9032	cd 99 93 	. . . 
	and a			;9035	a7 	. 
	jr z,$+8		;9036	28 06 	( . 
	res 6,(iy+000h)		;9038	fd cb 00 b6 	. . . . 
	jr $+53		;903c	18 33 	. 3 
	call 093b6h		;903e	cd b6 93 	. . . 
	jr $+48		;9041	18 2e 	. . 
	res 6,(iy+000h)		;9043	fd cb 00 b6 	. . . . 
	set 4,(iy+000h)		;9047	fd cb 00 e6 	. . . . 
	ld (iy+005h),000h		;904b	fd 36 05 00 	. 6 . . 
	push iy		;904f	fd e5 	. . 
	call 0c9a3h		;9051	cd a3 c9 	. . . 
	pop iy		;9054	fd e1 	. . 
	jr $+24		;9056	18 16 	. . 
	bit 5,a		;9058	cb 6f 	. o 
	jr z,$+20		;905a	28 12 	( . 
	res 5,a		;905c	cb af 	. . 
	set 3,a		;905e	cb df 	. . 
	ld (iy+000h),a		;9060	fd 77 00 	. w . 
	ld (iy+005h),000h		;9063	fd 36 05 00 	. 6 . . 
	push iy		;9067	fd e5 	. . 
	call 0c9b6h		;9069	cd b6 c9 	. . . 
	pop iy		;906c	fd e1 	. . 
	call 093ceh		;906e	cd ce 93 	. . . 
	ld a,000h		;9071	3e 00 	> . 
	ret			;9073	c9 	. 
	ld b,(iy+001h)		;9074	fd 46 01 	. F . 
	ld c,(iy+002h)		;9077	fd 4e 02 	. N . 
	bit 1,(iy+000h)		;907a	fd cb 00 4e 	. . . N 
	jr nz,$+6		;907e	20 04 	  . 
	inc b			;9080	04 	. 
	inc b			;9081	04 	. 
	jr $+4		;9082	18 02 	. . 
	dec b			;9084	05 	. 
	dec b			;9085	05 	. 
	bit 0,(iy+000h)		;9086	fd cb 00 46 	. . . F 
	jr nz,$+6		;908a	20 04 	  . 
	inc c			;908c	0c 	. 
	inc c			;908d	0c 	. 
	jr $+4		;908e	18 02 	. . 
	dec c			;9090	0d 	. 
	dec c			;9091	0d 	. 
	ld (iy+001h),b		;9092	fd 70 01 	. p . 
	ld (iy+002h),c		;9095	fd 71 02 	. q . 
	ret			;9098	c9 	. 
	ld de,00000h		;9099	11 00 00 	. . . 
	ld ix,0722ch		;909c	dd 21 2c 72 	. ! , r 
	ld b,005h		;90a0	06 05 	. . 
	bit 7,(ix+000h)		;90a2	dd cb 00 7e 	. . . ~ 
	jr z,$+120		;90a6	28 76 	( v 
	ld a,(ix+001h)		;90a8	dd 7e 01 	. ~ . 
	sub 009h		;90ab	d6 09 	. . 
	cp (iy+001h)		;90ad	fd be 01 	. . . 
	jr nc,$+110		;90b0	30 6c 	0 l 
	add a,011h		;90b2	c6 11 	. . 
	cp (iy+001h)		;90b4	fd be 01 	. . . 
	jr c,$+103		;90b7	38 65 	8 e 
	ld a,(ix+002h)		;90b9	dd 7e 02 	. ~ . 
	sub 008h		;90bc	d6 08 	. . 
	cp (iy+002h)		;90be	fd be 02 	. . . 
	jr z,$+4		;90c1	28 02 	( . 
	jr nc,$+91		;90c3	30 59 	0 Y 
	add a,010h		;90c5	c6 10 	. . 
	jr c,$+7		;90c7	38 05 	8 . 
	cp (iy+002h)		;90c9	fd be 02 	. . . 
	jr c,$+82		;90cc	38 50 	8 P 
	bit 5,(ix+000h)		;90ce	dd cb 00 6e 	. . . n 
	jr z,$+10		;90d2	28 08 	( . 
	set 4,(ix+000h)		;90d4	dd cb 00 e6 	. . . . 
	ld e,004h		;90d8	1e 04 	. . 
	jr $+82		;90da	18 50 	. P 
	ld a,(iy+001h)		;90dc	fd 7e 01 	. ~ . 
	cp (ix+001h)		;90df	dd be 01 	. . . 
	jr c,$+14		;90e2	38 0c 	8 . 
	bit 1,(iy+000h)		;90e4	fd cb 00 4e 	. . . N 
	jr z,$+20		;90e8	28 12 	( . 
	res 1,(iy+000h)		;90ea	fd cb 00 8e 	. . . . 
	jr $+12		;90ee	18 0a 	. . 
	bit 1,(iy+000h)		;90f0	fd cb 00 4e 	. . . N 
	jr nz,$+8		;90f4	20 06 	  . 
	set 1,(iy+000h)		;90f6	fd cb 00 ce 	. . . . 
	set 1,d		;90fa	cb ca 	. . 
	ld a,(iy+002h)		;90fc	fd 7e 02 	. ~ . 
	cp (ix+002h)		;90ff	dd be 02 	. . . 
	jr c,$+14		;9102	38 0c 	8 . 
	bit 0,(iy+000h)		;9104	fd cb 00 46 	. . . F 
	jr z,$+36		;9108	28 22 	( " 
	res 0,(iy+000h)		;910a	fd cb 00 86 	. . . . 
	jr $+12		;910e	18 0a 	. . 
	bit 0,(iy+000h)		;9110	fd cb 00 46 	. . . F 
	jr nz,$+10		;9114	20 08 	  . 
	set 0,(iy+000h)		;9116	fd cb 00 c6 	. . . . 
	set 0,d		;911a	cb c2 	. . 
	jr $+16		;911c	18 0e 	. . 
	inc ix		;911e	dd 23 	. # 
	inc ix		;9120	dd 23 	. # 
	inc ix		;9122	dd 23 	. # 
	inc ix		;9124	dd 23 	. # 
	inc ix		;9126	dd 23 	. # 
	dec b			;9128	05 	. 
	jp nz,090a2h		;9129	c2 a2 90 	. . . 
	ret			;912c	c9 	. 
	ld b,(iy+001h)		;912d	fd 46 01 	. F . 
	ld c,(iy+002h)		;9130	fd 4e 02 	. N . 
	dec b			;9133	05 	. 
	dec c			;9134	0d 	. 
	bit 1,(iy+000h)		;9135	fd cb 00 4e 	. . . N 
	jr nz,$+4		;9139	20 02 	  . 
	inc b			;913b	04 	. 
	inc b			;913c	04 	. 
	bit 0,(iy+000h)		;913d	fd cb 00 46 	. . . F 
	jr nz,$+4		;9141	20 02 	  . 
	inc c			;9143	0c 	. 
	inc c			;9144	0c 	. 
	ld e,000h		;9145	1e 00 	. . 
	push de			;9147	d5 	. 
	call 0ac3fh		;9148	cd 3f ac 	. ? . 
	pop de			;914b	d1 	. 
	ld a,(iy+001h)		;914c	fd 7e 01 	. ~ . 
	and 00fh		;914f	e6 0f 	. . 
	bit 1,(iy+000h)		;9151	fd cb 00 4e 	. . . N 
	jr z,$+53		;9155	28 33 	( 3 
	cp 00ah		;9157	fe 0a 	. . 
	jr nz,$+14		;9159	20 0c 	  . 
	set 7,e		;915b	cb fb 	. . 
	bit 4,(ix+000h)		;915d	dd cb 00 66 	. . . f 
	jr nz,$+90		;9161	20 58 	  X 
	set 1,e		;9163	cb cb 	. . 
	jr $+86		;9165	18 54 	. T 
	cp 002h		;9167	fe 02 	. . 
	jr nz,$+82		;9169	20 50 	  P 
	set 5,e		;916b	cb eb 	. . 
	ld a,(iy+002h)		;916d	fd 7e 02 	. ~ . 
	and 00fh		;9170	e6 0f 	. . 
	cp 008h		;9172	fe 08 	. . 
	jr nc,$+12		;9174	30 0a 	0 . 
	bit 0,(ix+000h)		;9176	dd cb 00 46 	. . . F 
	jr nz,$+65		;917a	20 3f 	  ? 
	set 1,e		;917c	cb cb 	. . 
	jr $+61		;917e	18 3b 	. ; 
	bit 1,(ix+000h)		;9180	dd cb 00 4e 	. . . N 
	jr nz,$+55		;9184	20 35 	  5 
	set 1,e		;9186	cb cb 	. . 
	jr $+51		;9188	18 31 	. 1 
	cp 006h		;918a	fe 06 	. . 
	jr nz,$+14		;918c	20 0c 	  . 
	set 7,e		;918e	cb fb 	. . 
	bit 5,(ix+000h)		;9190	dd cb 00 6e 	. . . n 
	jr nz,$+39		;9194	20 25 	  % 
	set 1,e		;9196	cb cb 	. . 
	jr $+35		;9198	18 21 	. ! 
	cp 00eh		;919a	fe 0e 	. . 
	jr nz,$+31		;919c	20 1d 	  . 
	set 5,e		;919e	cb eb 	. . 
	ld a,(iy+002h)		;91a0	fd 7e 02 	. ~ . 
	and 00fh		;91a3	e6 0f 	. . 
	cp 008h		;91a5	fe 08 	. . 
	jr nc,$+12		;91a7	30 0a 	0 . 
	bit 2,(ix+000h)		;91a9	dd cb 00 56 	. . . V 
	jr nz,$+14		;91ad	20 0c 	  . 
	set 1,e		;91af	cb cb 	. . 
	jr $+10		;91b1	18 08 	. . 
	bit 3,(ix+000h)		;91b3	dd cb 00 5e 	. . . ^ 
	jr nz,$+4		;91b7	20 02 	  . 
	set 1,e		;91b9	cb cb 	. . 
	ld a,(iy+002h)		;91bb	fd 7e 02 	. ~ . 
	and 00fh		;91be	e6 0f 	. . 
	bit 0,(iy+000h)		;91c0	fd cb 00 46 	. . . F 
	jr z,$+53		;91c4	28 33 	( 3 
	cp 002h		;91c6	fe 02 	. . 
	jr nz,$+14		;91c8	20 0c 	  . 
	set 6,e		;91ca	cb f3 	. . 
	bit 7,(ix+000h)		;91cc	dd cb 00 7e 	. . . ~ 
	jr nz,$+90		;91d0	20 58 	  X 
	set 0,e		;91d2	cb c3 	. . 
	jr $+86		;91d4	18 54 	. T 
	cp 00ah		;91d6	fe 0a 	. . 
	jr nz,$+82		;91d8	20 50 	  P 
	set 4,e		;91da	cb e3 	. . 
	ld a,(iy+001h)		;91dc	fd 7e 01 	. ~ . 
	and 00fh		;91df	e6 0f 	. . 
	cp 008h		;91e1	fe 08 	. . 
	jr c,$+12		;91e3	38 0a 	8 . 
	bit 2,(ix+000h)		;91e5	dd cb 00 56 	. . . V 
	jr nz,$+65		;91e9	20 3f 	  ? 
	set 0,e		;91eb	cb c3 	. . 
	jr $+61		;91ed	18 3b 	. ; 
	bit 0,(ix+000h)		;91ef	dd cb 00 46 	. . . F 
	jr nz,$+55		;91f3	20 35 	  5 
	set 0,e		;91f5	cb c3 	. . 
	jr $+51		;91f7	18 31 	. 1 
	cp 00eh		;91f9	fe 0e 	. . 
	jr nz,$+14		;91fb	20 0c 	  . 
	set 6,e		;91fd	cb f3 	. . 
	bit 6,(ix+000h)		;91ff	dd cb 00 76 	. . . v 
	jr nz,$+39		;9203	20 25 	  % 
	set 0,e		;9205	cb c3 	. . 
	jr $+35		;9207	18 21 	. ! 
	cp 006h		;9209	fe 06 	. . 
	jr nz,$+31		;920b	20 1d 	  . 
	set 4,e		;920d	cb e3 	. . 
	ld a,(iy+001h)		;920f	fd 7e 01 	. ~ . 
	and 00fh		;9212	e6 0f 	. . 
	cp 008h		;9214	fe 08 	. . 
	jr c,$+12		;9216	38 0a 	8 . 
	bit 3,(ix+000h)		;9218	dd cb 00 5e 	. . . ^ 
	jr nz,$+14		;921c	20 0c 	  . 
	set 0,e		;921e	cb c3 	. . 
	jr $+10		;9220	18 08 	. . 
	bit 1,(ix+000h)		;9222	dd cb 00 4e 	. . . N 
	jr nz,$+4		;9226	20 02 	  . 
	set 0,e		;9228	cb c3 	. . 
	bit 7,e		;922a	cb 7b 	. { 
	jr z,$+119		;922c	28 75 	( u 
	bit 6,e		;922e	cb 73 	. s 
	jr z,$+115		;9230	28 71 	( q 
	ld a,e			;9232	7b 	{ 
	and 003h		;9233	e6 03 	. . 
	jp nz,092e8h		;9235	c2 e8 92 	. . . 
	ld b,(iy+001h)		;9238	fd 46 01 	. F . 
	ld c,(iy+002h)		;923b	fd 4e 02 	. N . 
	ld a,b			;923e	78 	x 
	bit 1,(iy+000h)		;923f	fd cb 00 4e 	. . . N 
	jr z,$+50		;9243	28 30 	( 0 
	sub 004h		;9245	d6 04 	. . 
	ld b,a			;9247	47 	G 
	ld a,c			;9248	79 	y 
	bit 0,(iy+000h)		;9249	fd cb 00 46 	. . . F 
	jr z,$+22		;924d	28 14 	( . 
	sub 004h		;924f	d6 04 	. . 
	ld c,a			;9251	4f 	O 
	push de			;9252	d5 	. 
	call 0ac3fh		;9253	cd 3f ac 	. ? . 
	pop de			;9256	d1 	. 
	bit 3,(ix+000h)		;9257	dd cb 00 5e 	. . . ^ 
	jp nz,092e8h		;925b	c2 e8 92 	. . . 
	ld e,003h		;925e	1e 03 	. . 
	jp 092e8h		;9260	c3 e8 92 	. . . 
	add a,004h		;9263	c6 04 	. . 
	ld c,a			;9265	4f 	O 
	push de			;9266	d5 	. 
	call 0ac3fh		;9267	cd 3f ac 	. ? . 
	pop de			;926a	d1 	. 
	bit 2,(ix+000h)		;926b	dd cb 00 56 	. . . V 
	jr nz,$+121		;926f	20 77 	  w 
	ld e,003h		;9271	1e 03 	. . 
	jr $+117		;9273	18 73 	. s 
	add a,004h		;9275	c6 04 	. . 
	ld b,a			;9277	47 	G 
	ld a,c			;9278	79 	y 
	bit 0,(iy+000h)		;9279	fd cb 00 46 	. . . F 
	jr z,$+20		;927d	28 12 	( . 
	sub 004h		;927f	d6 04 	. . 
	ld c,a			;9281	4f 	O 
	push de			;9282	d5 	. 
	call 0ac3fh		;9283	cd 3f ac 	. ? . 
	pop de			;9286	d1 	. 
	bit 1,(ix+000h)		;9287	dd cb 00 4e 	. . . N 
	jr nz,$+93		;928b	20 5b 	  [ 
	ld e,003h		;928d	1e 03 	. . 
	jr $+89		;928f	18 57 	. W 
	add a,004h		;9291	c6 04 	. . 
	ld c,a			;9293	4f 	O 
	push de			;9294	d5 	. 
	call 0ac3fh		;9295	cd 3f ac 	. ? . 
	pop de			;9298	d1 	. 
	bit 0,(ix+000h)		;9299	dd cb 00 46 	. . . F 
	jr nz,$+75		;929d	20 49 	  I 
	ld e,003h		;929f	1e 03 	. . 
	jr $+71		;92a1	18 45 	. E 
	bit 5,e		;92a3	cb 6b 	. k 
	jr z,$+67		;92a5	28 41 	( A 
	bit 4,e		;92a7	cb 63 	. c 
	jr z,$+63		;92a9	28 3d 	( = 
	ld a,e			;92ab	7b 	{ 
	and 003h		;92ac	e6 03 	. . 
	jr nz,$+58		;92ae	20 38 	  8 
	bit 1,(iy+000h)		;92b0	fd cb 00 4e 	. . . N 
	jr z,$+28		;92b4	28 1a 	( . 
	bit 0,(iy+000h)		;92b6	fd cb 00 46 	. . . F 
	jr z,$+12		;92ba	28 0a 	( . 
	bit 0,(ix+000h)		;92bc	dd cb 00 46 	. . . F 
	jr nz,$+40		;92c0	20 26 	  & 
	ld e,003h		;92c2	1e 03 	. . 
	jr $+36		;92c4	18 22 	. " 
	bit 1,(ix+000h)		;92c6	dd cb 00 4e 	. . . N 
	jr nz,$+30		;92ca	20 1c 	  . 
	ld e,003h		;92cc	1e 03 	. . 
	jr $+26		;92ce	18 18 	. . 
	bit 0,(iy+000h)		;92d0	fd cb 00 46 	. . . F 
	jr z,$+12		;92d4	28 0a 	( . 
	bit 2,(ix+000h)		;92d6	dd cb 00 56 	. . . V 
	jr nz,$+14		;92da	20 0c 	  . 
	ld e,003h		;92dc	1e 03 	. . 
	jr $+10		;92de	18 08 	. . 
	bit 3,(ix+000h)		;92e0	dd cb 00 5e 	. . . ^ 
	jr nz,$+4		;92e4	20 02 	  . 
	ld e,003h		;92e6	1e 03 	. . 
	ld a,e			;92e8	7b 	{ 
	and 003h		;92e9	e6 03 	. . 
	xor (iy+000h)		;92eb	fd ae 00 	. . . 
	ld (iy+000h),a		;92ee	fd 77 00 	. w . 
	ret			;92f1	c9 	. 
	ld ix,0728eh		;92f2	dd 21 8e 72 	. ! . r 
	ld c,000h		;92f6	0e 00 	. . 
	bit 7,(ix+004h)		;92f8	dd cb 04 7e 	. . . ~ 
	jr z,$+26		;92fc	28 18 	( . 
	bit 6,(ix+004h)		;92fe	dd cb 04 76 	. . . v 
	jr nz,$+20		;9302	20 12 	  . 
	push bc			;9304	c5 	. 
	push ix		;9305	dd e5 	. . 
	ld b,(ix+002h)		;9307	dd 46 02 	. F . 
	ld c,(ix+001h)		;930a	dd 4e 01 	. N . 
	call 0b5ddh		;930d	cd dd b5 	. . . 
	pop ix		;9310	dd e1 	. . 
	pop bc			;9312	c1 	. 
	and a			;9313	a7 	. 
	jr nz,$+16		;9314	20 0e 	  . 
	ld de,00006h		;9316	11 06 00 	. . . 
	add ix,de		;9319	dd 19 	. . 
	inc c			;931b	0c 	. 
	ld a,c			;931c	79 	y 
	cp 007h		;931d	fe 07 	. . 
	jr c,$-39		;931f	38 d7 	8 . 
	xor a			;9321	af 	. 
	jr $+20		;9322	18 12 	. . 
	call 0b7c4h		;9324	cd c4 b7 	. . . 
	push af			;9327	f5 	. 
	ld de,00032h		;9328	11 32 00 	. 2 . 
	call 0b601h		;932b	cd 01 b6 	. . . 
	pop af			;932e	f1 	. 
	and a			;932f	a7 	. 
	ld a,002h		;9330	3e 02 	> . 
	jr z,$+4		;9332	28 02 	( . 
	ld a,001h		;9334	3e 01 	> . 
	ret			;9336	c9 	. 
	ld ix,072c7h		;9337	dd 21 c7 72 	. ! . r 
	ld c,000h		;933b	0e 00 	. . 
	bit 7,(ix+004h)		;933d	dd cb 04 7e 	. . . ~ 
	jr z,$+20		;9341	28 12 	( . 
	push bc			;9343	c5 	. 
	push ix		;9344	dd e5 	. . 
	ld b,(ix+002h)		;9346	dd 46 02 	. F . 
	ld c,(ix+001h)		;9349	dd 4e 01 	. N . 
	call 0b5ddh		;934c	cd dd b5 	. . . 
	pop ix		;934f	dd e1 	. . 
	pop bc			;9351	c1 	. 
	and a			;9352	a7 	. 
	jr nz,$+16		;9353	20 0e 	  . 
	ld de,00006h		;9355	11 06 00 	. . . 
	add ix,de		;9358	dd 19 	. . 
	inc c			;935a	0c 	. 
	ld a,c			;935b	79 	y 
	cp 003h		;935c	fe 03 	. . 
	jr c,$-33		;935e	38 dd 	8 . 
	xor a			;9360	af 	. 
	jr $+13		;9361	18 0b 	. . 
	call 0b832h		;9363	cd 32 b8 	. 2 . 
	ld de,00032h		;9366	11 32 00 	. 2 . 
	call 0b601h		;9369	cd 01 b6 	. . . 
	ld a,001h		;936c	3e 01 	> . 
	ret			;936e	c9 	. 
	ld a,(072bdh)		;936f	3a bd 72 	: . r 
	bit 6,a		;9372	cb 77 	. w 
	jr z,$+36		;9374	28 22 	( " 
	ld a,(072bfh)		;9376	3a bf 72 	: . r 
	ld b,a			;9379	47 	G 
	ld a,(072beh)		;937a	3a be 72 	: . r 
	ld c,a			;937d	4f 	O 
	call 0b5ddh		;937e	cd dd b5 	. . . 
	and a			;9381	a7 	. 
	jr z,$+22		;9382	28 14 	( . 
	ld bc,00808h		;9384	01 08 08 	. . . 
	ld d,000h		;9387	16 00 	. . 
	ld a,003h		;9389	3e 03 	> . 
	call 0b629h		;938b	cd 29 b6 	. ) . 
	ld de,00032h		;938e	11 32 00 	. 2 . 
	call 0b601h		;9391	cd 01 b6 	. . . 
	call 0b76dh		;9394	cd 6d b7 	. m . 
	inc a			;9397	3c 	< 
	ret			;9398	c9 	. 
	ld a,(07284h)		;9399	3a 84 72 	: . r 
	ld b,a			;939c	47 	G 
	ld a,(07285h)		;939d	3a 85 72 	: . r 
	ld c,a			;93a0	4f 	O 
	call 0b5ddh		;93a1	cd dd b5 	. . . 
	and a			;93a4	a7 	. 
	jr z,$+16		;93a5	28 0e 	( . 
	ld hl,07281h		;93a7	21 81 72 	! . r 
	set 6,(hl)		;93aa	cb f6 	. . 
	push iy		;93ac	fd e5 	. . 
	call 0c98ah		;93ae	cd 8a c9 	. . . 
	pop iy		;93b1	fd e1 	. . 
	ld a,001h		;93b3	3e 01 	> . 
	ret			;93b5	c9 	. 
	ld b,(iy+001h)		;93b6	fd 46 01 	. F . 
	ld c,(iy+002h)		;93b9	fd 4e 02 	. N . 
	ld d,001h		;93bc	16 01 	. . 
	ld a,004h		;93be	3e 04 	> . 
	call 0b629h		;93c0	cd 29 b6 	. ) . 
	ld hl,00001h		;93c3	21 01 00 	! . . 
	xor a			;93c6	af 	. 
	call 01fcdh		;93c7	cd cd 1f 	. . . 
	ld (iy+003h),a		;93ca	fd 77 03 	. w . 
	ret			;93cd	c9 	. 
	ld a,(iy+005h)		;93ce	fd 7e 05 	. ~ . 
	add a,002h		;93d1	c6 02 	. . 
	ld b,(iy+001h)		;93d3	fd 46 01 	. F . 
	ld c,(iy+002h)		;93d6	fd 4e 02 	. N . 
	bit 3,(iy+000h)		;93d9	fd cb 00 5e 	. . . ^ 
	jr z,$+16		;93dd	28 0e 	( . 
	ld c,a			;93df	4f 	O 
	ld a,009h		;93e0	3e 09 	> . 
	sub c			;93e2	91 	. 
	ld ix,07281h		;93e3	dd 21 81 72 	. ! . r 
	ld b,(ix+003h)		;93e7	dd 46 03 	. F . 
	ld c,(ix+004h)		;93ea	dd 4e 04 	. N . 
	ld d,a			;93ed	57 	W 
	ld a,004h		;93ee	3e 04 	> . 
	call 0b629h		;93f0	cd 29 b6 	. ) . 
	inc (iy+005h)		;93f3	fd 34 05 	. 4 . 
	ld a,(iy+005h)		;93f6	fd 7e 05 	. ~ . 
	cp 006h		;93f9	fe 06 	. . 
	jr z,$+14		;93fb	28 0c 	( . 
	ld hl,00005h		;93fd	21 05 00 	! . . 
	xor a			;9400	af 	. 
	call 01fcdh		;9401	cd cd 1f 	. . . 
	ld (iy+003h),a		;9404	fd 77 03 	. w . 
	jr $+70		;9407	18 44 	. D 
	bit 4,(iy+000h)		;9409	fd cb 00 66 	. . . f 
	jr z,$+55		;940d	28 35 	( 5 
	res 4,(iy+000h)		;940f	fd cb 00 a6 	. . . . 
	set 5,(iy+000h)		;9413	fd cb 00 ee 	. . . . 
	ld a,(iy+004h)		;9417	fd 7e 04 	. ~ . 
	dec a			;941a	3d 	= 
	cp 004h		;941b	fe 04 	. . 
	jr c,$+4		;941d	38 02 	8 . 
	ld a,004h		;941f	3e 04 	> . 
	add a,a			;9421	87 	. 
	ld e,a			;9422	5f 	_ 
	ld d,000h		;9423	16 00 	. . 
	ld ix,0944eh		;9425	dd 21 4e 94 	. ! N . 
	add ix,de		;9429	dd 19 	. . 
	ld l,(ix+000h)		;942b	dd 6e 00 	. n . 
	ld h,(ix+001h)		;942e	dd 66 01 	. f . 
	xor a			;9431	af 	. 
	call 01fcdh		;9432	cd cd 1f 	. . . 
	ld (iy+003h),a		;9435	fd 77 03 	. w . 
	ld bc,00808h		;9438	01 08 08 	. . . 
	ld d,000h		;943b	16 00 	. . 
	ld a,004h		;943d	3e 04 	> . 
	call 0b629h		;943f	cd 29 b6 	. ) . 
	jr $+11		;9442	18 09 	. . 
	res 3,(iy+000h)		;9444	fd cb 00 9e 	. . . . 
	ld hl,07281h		;9448	21 81 72 	! . r 
	set 6,(hl)		;944b	cb f6 	. . 
	ret			;944d	c9 	. 
	inc a			;944e	3c 	< 
	nop			;944f	00 	. 
	ld a,b			;9450	78 	x 
	nop			;9451	00 	. 
	ret p			;9452	f0 	. 
	nop			;9453	00 	. 
	ld l,b			;9454	68 	h 
	ld bc,001e0h		;9455	01 e0 01 	. . . 
	nop			;9458	00 	. 
	ld a,(0726eh)		;9459	3a 6e 72 	: n r 
	bit 6,a		;945c	cb 77 	. w 
	jr z,$+5		;945e	28 03 	( . 
	xor a			;9460	af 	. 
	jr $+71		;9461	18 45 	. E 
	ld iy,07281h		;9463	fd 21 81 72 	. ! . r 
	ld a,(iy+002h)		;9467	fd 7e 02 	. ~ . 
	call 01fd0h		;946a	cd d0 1f 	. . . 
	and a			;946d	a7 	. 
	jr z,$+44		;946e	28 2a 	( * 
	call 094a9h		;9470	cd a9 94 	. . . 
	and a			;9473	a7 	. 
	jr nz,$+6		;9474	20 04 	  . 
	ld a,001h		;9476	3e 01 	> . 
	jr $+17		;9478	18 0f 	. . 
	cp 005h		;947a	fe 05 	. . 
	jr nz,$+7		;947c	20 05 	  . 
	jp 0d366h		;947e	c3 66 d3 	. f . 
	jr $+16		;9481	18 0e 	. . 
	ld (iy+001h),a		;9483	fd 77 01 	. w . 
	call 095a1h		;9486	cd a1 95 	. . . 
	push af			;9489	f5 	. 
	call 09670h		;948a	cd 70 96 	. p . 
	call 096e4h		;948d	cd e4 96 	. . . 
	pop af			;9490	f1 	. 
	call 09732h		;9491	cd 32 97 	. 2 . 
	call 09807h		;9494	cd 07 98 	. . . 
	and a			;9497	a7 	. 
	jr nz,$+16		;9498	20 0e 	  . 
	ld hl,07245h		;949a	21 45 72 	! E r 
	ld b,014h		;949d	06 14 	. . 
	xor a			;949f	af 	. 
	cp (hl)			;94a0	be 	. 
	jr nz,$+7		;94a1	20 05 	  . 
	inc hl			;94a3	23 	# 
	djnz $-4		;94a4	10 fa 	. . 
	ld a,002h		;94a6	3e 02 	> . 
	ret			;94a8	c9 	. 
	ld ix,07088h		;94a9	dd 21 88 70 	. ! . p 
	ld a,(0726eh)		;94ad	3a 6e 72 	: n r 
	bit 1,a		;94b0	cb 4f 	. O 
	jr z,$+6		;94b2	28 04 	( . 
	ld ix,0708dh		;94b4	dd 21 8d 70 	. ! . p 
	bit 6,(ix+000h)		;94b8	dd cb 00 76 	. . . v 
	jr nz,$+8		;94bc	20 06 	  . 
	bit 6,(ix+003h)		;94be	dd cb 03 76 	. . . v 
	jr z,$+118		;94c2	28 74 	( t 
	ld a,(07281h)		;94c4	3a 81 72 	: . r 
	bit 6,a		;94c7	cb 77 	. w 
	jr z,$+111		;94c9	28 6d 	( m 
	ld b,(iy+003h)		;94cb	fd 46 03 	. F . 
	ld c,(iy+004h)		;94ce	fd 4e 04 	. N . 
	ld a,(iy+001h)		;94d1	fd 7e 01 	. ~ . 
	cp 003h		;94d4	fe 03 	. . 
	jr nc,$+39		;94d6	30 25 	0 % 
	cp 001h		;94d8	fe 01 	. . 
	ld a,c			;94da	79 	y 
	jr nz,$+18		;94db	20 10 	  . 
	add a,006h		;94dd	c6 06 	. . 
	ld (072dbh),a		;94df	32 db 72 	2 . r 
	add a,003h		;94e2	c6 03 	. . 
	jr c,$+84		;94e4	38 52 	8 R 
	ld c,a			;94e6	4f 	O 
	ld a,b			;94e7	78 	x 
	ld (072dah),a		;94e8	32 da 72 	2 . r 
	jr $+57		;94eb	18 37 	. 7 
	sub 006h		;94ed	d6 06 	. . 
	ld (072dbh),a		;94ef	32 db 72 	2 . r 
	sub 003h		;94f2	d6 03 	. . 
	jr c,$+68		;94f4	38 42 	8 B 
	ld c,a			;94f6	4f 	O 
	ld a,b			;94f7	78 	x 
	ld (072dah),a		;94f8	32 da 72 	2 . r 
	jr $+41		;94fb	18 27 	. ' 
	cp 003h		;94fd	fe 03 	. . 
	ld a,b			;94ff	78 	x 
	jr nz,$+20		;9500	20 12 	  . 
	sub 006h		;9502	d6 06 	. . 
	ld (072dah),a		;9504	32 da 72 	2 . r 
	sub 003h		;9507	d6 03 	. . 
	cp 01ch		;9509	fe 1c 	. . 
	jr c,$+45		;950b	38 2b 	8 + 
	ld b,a			;950d	47 	G 
	ld a,c			;950e	79 	y 
	ld (072dbh),a		;950f	32 db 72 	2 . r 
	jr $+18		;9512	18 10 	. . 
	add a,006h		;9514	c6 06 	. . 
	ld (072dah),a		;9516	32 da 72 	2 . r 
	add a,003h		;9519	c6 03 	. . 
	cp 0b5h		;951b	fe b5 	. . 
	jr nc,$+27		;951d	30 19 	0 . 
	ld b,a			;951f	47 	G 
	ld a,c			;9520	79 	y 
	ld (072dbh),a		;9521	32 db 72 	2 . r 
	push ix		;9524	dd e5 	. . 
	call 0ac3fh		;9526	cd 3f ac 	. ? . 
	ld a,(ix+000h)		;9529	dd 7e 00 	. ~ . 
	pop ix		;952c	dd e1 	. . 
	and 00fh		;952e	e6 0f 	. . 
	cp 00fh		;9530	fe 0f 	. . 
	jr nz,$+6		;9532	20 04 	  . 
	ld a,005h		;9534	3e 05 	> . 
	jr $+64		;9536	18 3e 	. > 
	ld a,001h		;9538	3e 01 	> . 
	bit 1,(ix+001h)		;953a	dd cb 01 4e 	. . . N 
	jr nz,$+26		;953e	20 18 	  . 
	inc a			;9540	3c 	< 
	bit 3,(ix+001h)		;9541	dd cb 01 5e 	. . . ^ 
	jr nz,$+19		;9545	20 11 	  . 
	inc a			;9547	3c 	< 
	bit 0,(ix+001h)		;9548	dd cb 01 46 	. . . F 
	jr nz,$+12		;954c	20 0a 	  . 
	inc a			;954e	3c 	< 
	bit 2,(ix+001h)		;954f	dd cb 01 56 	. . . V 
	jr nz,$+5		;9553	20 03 	  . 
	xor a			;9555	af 	. 
	jr $+32		;9556	18 1e 	. . 
	push af			;9558	f5 	. 
	cp 003h		;9559	fe 03 	. . 
	jr nc,$+11		;955b	30 09 	0 . 
	ld a,(iy+003h)		;955d	fd 7e 03 	. ~ . 
	and 00fh		;9560	e6 0f 	. . 
	jr nz,$+13		;9562	20 0b 	  . 
	jr $+17		;9564	18 0f 	. . 
	ld a,(iy+004h)		;9566	fd 7e 04 	. ~ . 
	and 00fh		;9569	e6 0f 	. . 
	cp 008h		;956b	fe 08 	. . 
	jr z,$+8		;956d	28 06 	( . 
	pop af			;956f	f1 	. 
	ld a,(iy+001h)		;9570	fd 7e 01 	. ~ . 
	jr $+3		;9573	18 01 	. . 
	pop af			;9575	f1 	. 
	ret			;9576	c9 	. 
	ld ix,072d9h		;9577	dd 21 d9 72 	. ! . r 
	ld a,(iy+001h)		;957b	fd 7e 01 	. ~ . 
	dec a			;957e	3d 	= 
	ld b,a			;957f	47 	G 
	cp 002h		;9580	fe 02 	. . 
	jr c,$+17		;9582	38 0f 	8 . 
	ld b,003h		;9584	06 03 	. . 
	cp 002h		;9586	fe 02 	. . 
	jr z,$+4		;9588	28 02 	( . 
	ld b,001h		;958a	06 01 	. . 
	bit 7,(iy+004h)		;958c	fd cb 04 7e 	. . . ~ 
	jr z,$+3		;9590	28 01 	( . 
	dec b			;9592	05 	. 
	set 7,b		;9593	cb f8 	. . 
	ld (ix+000h),b		;9595	dd 70 00 	. p . 
	set 3,(iy+000h)		;9598	fd cb 00 de 	. . . . 
	res 6,(iy+000h)		;959c	fd cb 00 b6 	. . . . 
	ret			;95a0	c9 	. 
	call 0961fh		;95a1	cd 1f 96 	. . . 
	and a			;95a4	a7 	. 
	jp nz,0961ch		;95a5	c2 1c 96 	. . . 
	push bc			;95a8	c5 	. 
	res 5,(iy+000h)		;95a9	fd cb 00 ae 	. . . . 
	ld b,(iy+003h)		;95ad	fd 46 03 	. F . 
	ld c,(iy+004h)		;95b0	fd 4e 04 	. N . 
	ld a,(iy+001h)		;95b3	fd 7e 01 	. ~ . 
	cp 003h		;95b6	fe 03 	. . 
	jr nc,$+22		;95b8	30 14 	0 . 
	ld d,a			;95ba	57 	W 
	ld a,001h		;95bb	3e 01 	> . 
	call 0aee1h		;95bd	cd e1 ae 	. . . 
	bit 0,a		;95c0	cb 47 	. G 
	jr z,$+6		;95c2	28 04 	( . 
	set 5,(iy+000h)		;95c4	fd cb 00 ee 	. . . . 
	cp 002h		;95c8	fe 02 	. . 
	jr nc,$+77		;95ca	30 4b 	0 K 
	jr $+9		;95cc	18 07 	. . 
	ld d,a			;95ce	57 	W 
	call 0b12dh		;95cf	cd 2d b1 	. - . 
	and a			;95d2	a7 	. 
	jr nz,$+68		;95d3	20 42 	  B 
	pop bc			;95d5	c1 	. 
	ld (iy+003h),b		;95d6	fd 70 03 	. p . 
	ld (iy+004h),c		;95d9	fd 71 04 	. q . 
	ld a,(iy+001h)		;95dc	fd 7e 01 	. ~ . 
	ld d,a			;95df	57 	W 
	cp 001h		;95e0	fe 01 	. . 
	jr nz,$+7		;95e2	20 05 	  . 
	call 0b2fah		;95e4	cd fa b2 	. . . 
	jr $+23		;95e7	18 15 	. . 
	cp 002h		;95e9	fe 02 	. . 
	jr nz,$+7		;95eb	20 05 	  . 
	call 0b39dh		;95ed	cd 9d b3 	. . . 
	jr $+14		;95f0	18 0c 	. . 
	cp 003h		;95f2	fe 03 	. . 
	jr nz,$+7		;95f4	20 05 	  . 
	call 0b43fh		;95f6	cd 3f b4 	. ? . 
	jr $+5		;95f9	18 03 	. . 
	call 0b4e9h		;95fb	cd e9 b4 	. . . 
	bit 0,e		;95fe	cb 43 	. C 
	jr z,$+6		;9600	28 04 	( . 
	set 4,(iy+000h)		;9602	fd cb 00 e6 	. . . . 
	ld b,(iy+003h)		;9606	fd 46 03 	. F . 
	ld c,(iy+004h)		;9609	fd 4e 04 	. N . 
	push de			;960c	d5 	. 
	call 0ac3fh		;960d	cd 3f ac 	. ? . 
	call 0aeb7h		;9610	cd b7 ae 	. . . 
	pop de			;9613	d1 	. 
	xor a			;9614	af 	. 
	jr $+9		;9615	18 07 	. . 
	set 5,(iy+000h)		;9617	fd cb 00 ee 	. . . . 
	pop bc			;961b	c1 	. 
	ld a,001h		;961c	3e 01 	> . 
	ret			;961e	c9 	. 
	ld (iy+001h),a		;961f	fd 77 01 	. w . 
	ld b,(iy+003h)		;9622	fd 46 03 	. F . 
	ld c,(iy+004h)		;9625	fd 4e 04 	. N . 
	cp 003h		;9628	fe 03 	. . 
	jr nc,$+33		;962a	30 1f 	0 . 
	ld a,b			;962c	78 	x 
	and 00fh		;962d	e6 0f 	. . 
	jr nz,$+62		;962f	20 3c 	  < 
	ld a,c			;9631	79 	y 
	add a,004h		;9632	c6 04 	. . 
	ld c,a			;9634	4f 	O 
	ld a,(iy+001h)		;9635	fd 7e 01 	. ~ . 
	cp 001h		;9638	fe 01 	. . 
	jr z,$+6		;963a	28 04 	( . 
	ld a,c			;963c	79 	y 
	sub 008h		;963d	d6 08 	. . 
	ld c,a			;963f	4f 	O 
	ld a,c			;9640	79 	y 
	cp 018h		;9641	fe 18 	. . 
	jr c,$+42		;9643	38 28 	8 ( 
	cp 0e9h		;9645	fe e9 	. . 
	jr nc,$+38		;9647	30 24 	0 $ 
	jr $+33		;9649	18 1f 	. . 
	ld a,c			;964b	79 	y 
	and 00fh		;964c	e6 0f 	. . 
	cp 008h		;964e	fe 08 	. . 
	jr nz,$+29		;9650	20 1b 	  . 
	ld a,b			;9652	78 	x 
	add a,004h		;9653	c6 04 	. . 
	ld b,a			;9655	47 	G 
	ld a,(iy+001h)		;9656	fd 7e 01 	. ~ . 
	cp 004h		;9659	fe 04 	. . 
	jr z,$+6		;965b	28 04 	( . 
	ld a,b			;965d	78 	x 
	sub 008h		;965e	d6 08 	. . 
	ld b,a			;9660	47 	G 
	ld a,b			;9661	78 	x 
	cp 020h		;9662	fe 20 	.   
	jr c,$+9		;9664	38 07 	8 . 
	cp 0b1h		;9666	fe b1 	. . 
	jr nc,$+5		;9668	30 03 	0 . 
	xor a			;966a	af 	. 
	jr $+4		;966b	18 02 	. . 
	ld a,001h		;966d	3e 01 	> . 
	ret			;966f	c9 	. 
	call 0b173h		;9670	cd 73 b1 	. s . 
	jr c,$+34		;9673	38 20 	8   
	bit 1,(iy+000h)		;9675	fd cb 00 4e 	. . . N 
	jr z,$+106		;9679	28 68 	( h 
	ld a,(iy+008h)		;967b	fd 7e 08 	. ~ . 
	call 01fd0h		;967e	cd d0 1f 	. . . 
	and a			;9681	a7 	. 
	jr z,$+97		;9682	28 5f 	( _ 
	ld (iy+007h),000h		;9684	fd 36 07 00 	. 6 . . 
	res 1,(iy+000h)		;9688	fd cb 00 8e 	. . . . 
	push iy		;968c	fd e5 	. . 
	call 0c97fh		;968e	cd 7f c9 	.  . 
	pop iy		;9691	fd e1 	. . 
	jr $+80		;9693	18 4e 	. N 
	ld de,00005h		;9695	11 05 00 	. . . 
	call 0b601h		;9698	cd 01 b6 	. . . 
	bit 1,(iy+000h)		;969b	fd cb 00 4e 	. . . N 
	jr z,$+43		;969f	28 29 	( ) 
	ld a,(iy+008h)		;96a1	fd 7e 08 	. ~ . 
	call 01fd0h		;96a4	cd d0 1f 	. . . 
	and a			;96a7	a7 	. 
	jr nz,$+34		;96a8	20 20 	    
	ld a,(iy+008h)		;96aa	fd 7e 08 	. ~ . 
	call 01fcah		;96ad	cd ca 1f 	. . . 
	inc (iy+007h)		;96b0	fd 34 07 	. 4 . 
	ld a,(iy+007h)		;96b3	fd 7e 07 	. ~ . 
	cp 008h		;96b6	fe 08 	. . 
	jr c,$+29		;96b8	38 1b 	8 . 
	ld (iy+007h),000h		;96ba	fd 36 07 00 	. 6 . . 
	ld de,00032h		;96be	11 32 00 	. 2 . 
	call 0b601h		;96c1	cd 01 b6 	. . . 
	res 1,(iy+000h)		;96c4	fd cb 00 8e 	. . . . 
	jr $+27		;96c8	18 19 	. . 
	ld (iy+007h),001h		;96ca	fd 36 07 01 	. 6 . . 
	push iy		;96ce	fd e5 	. . 
	call 0c985h		;96d0	cd 85 c9 	. . . 
	pop iy		;96d3	fd e1 	. . 
	xor a			;96d5	af 	. 
	ld hl,0001eh		;96d6	21 1e 00 	! . . 
	call 01fcdh		;96d9	cd cd 1f 	. . . 
	ld (iy+008h),a		;96dc	fd 77 08 	. w . 
	set 1,(iy+000h)		;96df	fd cb 00 ce 	. . . . 
	ret			;96e3	c9 	. 
	ld a,(07272h)		;96e4	3a 72 72 	: r r 
	bit 7,a		;96e7	cb 7f 	.  
	jr z,$+72		;96e9	28 46 	( F 
	ld a,(iy+003h)		;96eb	fd 7e 03 	. ~ . 
	cp 060h		;96ee	fe 60 	. ` 
	jr nz,$+65		;96f0	20 3f 	  ? 
	ld a,(iy+004h)		;96f2	fd 7e 04 	. ~ . 
	cp 078h		;96f5	fe 78 	. x 
	jr nz,$+58		;96f7	20 38 	  8 
	ld hl,07272h		;96f9	21 72 72 	! r r 
	res 7,(hl)		;96fc	cb be 	. . 
	ld a,(hl)			;96fe	7e 	~ 
	or 032h		;96ff	f6 32 	. 2 
	ld (hl),a			;9701	77 	w 
	ld a,00ah		;9702	3e 0a 	> . 
	ld (0728ch),a		;9704	32 8c 72 	2 . r 
	ld hl,(0727dh)		;9707	2a 7d 72 	* } r 
	ld a,(0726eh)		;970a	3a 6e 72 	: n r 
	ld c,a			;970d	4f 	O 
	ld a,(07274h)		;970e	3a 74 72 	: t r 
	bit 1,c		;9711	cb 49 	. I 
	jr z,$+8		;9713	28 06 	( . 
	ld hl,(0727fh)		;9715	2a 7f 72 	*  r 
	ld a,(07275h)		;9718	3a 75 72 	: u r 
	ld hl,00000h		;971b	21 00 00 	! . . 
	ld de,00032h		;971e	11 32 00 	. 2 . 
	add hl,de			;9721	19 	. 
	dec a			;9722	3d 	= 
	jp p,09721h		;9723	f2 21 97 	. ! . 
	ex de,hl			;9726	eb 	. 
	call 0b601h		;9727	cd 01 b6 	. . . 
	push iy		;972a	fd e5 	. . 
	nop			;972c	00 	. 
	nop			;972d	00 	. 
	nop			;972e	00 	. 
	pop iy		;972f	fd e1 	. . 
	ret			;9731	c9 	. 
	and a			;9732	a7 	. 
	jr nz,$+10		;9733	20 08 	  . 
	ld a,(iy+006h)		;9735	fd 7e 06 	. ~ . 
	inc a			;9738	3c 	< 
	cp 002h		;9739	fe 02 	. . 
	jr c,$+3		;973b	38 01 	8 . 
	xor a			;973d	af 	. 
	ld (iy+006h),a		;973e	fd 77 06 	. w . 
	ld c,001h		;9741	0e 01 	. . 
	add a,c			;9743	81 	. 
	bit 5,(iy+000h)		;9744	fd cb 00 6e 	. . . n 
	jr z,$+4		;9748	28 02 	( . 
	add a,002h		;974a	c6 02 	. . 
	ld c,a			;974c	4f 	O 
	ld a,(iy+001h)		;974d	fd 7e 01 	. ~ . 
	cp 002h		;9750	fe 02 	. . 
	jr nz,$+8		;9752	20 06 	  . 
	ld a,c			;9754	79 	y 
	add a,007h		;9755	c6 07 	. . 
	ld c,a			;9757	4f 	O 
	jr $+46		;9758	18 2c 	. , 
	cp 003h		;975a	fe 03 	. . 
	jr nz,$+21		;975c	20 13 	  . 
	ld a,(iy+004h)		;975e	fd 7e 04 	. ~ . 
	and a			;9761	a7 	. 
	jp p,0976bh		;9762	f2 6b 97 	. k . 
	ld a,c			;9765	79 	y 
	add a,00eh		;9766	c6 0e 	. . 
	ld c,a			;9768	4f 	O 
	jr $+29		;9769	18 1b 	. . 
	ld a,c			;976b	79 	y 
	add a,01ch		;976c	c6 1c 	. . 
	ld c,a			;976e	4f 	O 
	jr $+23		;976f	18 15 	. . 
	cp 004h		;9771	fe 04 	. . 
	jr nz,$+19		;9773	20 11 	  . 
	ld a,(iy+004h)		;9775	fd 7e 04 	. ~ . 
	and a			;9778	a7 	. 
	jp p,09782h		;9779	f2 82 97 	. . . 
	ld a,c			;977c	79 	y 
	add a,015h		;977d	c6 15 	. . 
	ld c,a			;977f	4f 	O 
	jr $+6		;9780	18 04 	. . 
	ld a,c			;9782	79 	y 
	add a,023h		;9783	c6 23 	. # 
	ld c,a			;9785	4f 	O 
	ld (iy+005h),c		;9786	fd 71 05 	. q . 
	bit 6,(iy+000h)		;9789	fd cb 00 76 	. . . v 
	jr z,$+59		;978d	28 39 	( 9 
	ld a,(iy+001h)		;978f	fd 7e 01 	. ~ . 
	cp 003h		;9792	fe 03 	. . 
	jr c,$+13		;9794	38 0b 	8 . 
	ld e,a			;9796	5f 	_ 
	ld a,(iy+004h)		;9797	fd 7e 04 	. ~ . 
	and a			;979a	a7 	. 
	ld a,e			;979b	7b 	{ 
	jp m,097a1h		;979c	fa a1 97 	. . . 
	add a,002h		;979f	c6 02 	. . 
	bit 5,(iy+000h)		;97a1	fd cb 00 6e 	. . . n 
	jr z,$+4		;97a5	28 02 	( . 
	add a,006h		;97a7	c6 06 	. . 
	dec a			;97a9	3d 	= 
	add a,a			;97aa	87 	. 
	ld e,a			;97ab	5f 	_ 
	ld d,000h		;97ac	16 00 	. . 
	ld hl,097efh		;97ae	21 ef 97 	! . . 
	add hl,de			;97b1	19 	. 
	ld a,(iy+004h)		;97b2	fd 7e 04 	. ~ . 
	add a,008h		;97b5	c6 08 	. . 
	sub (hl)			;97b7	96 	. 
	ld c,a			;97b8	4f 	O 
	inc hl			;97b9	23 	# 
	ld a,(iy+003h)		;97ba	fd 7e 03 	. ~ . 
	add a,008h		;97bd	c6 08 	. . 
	sub (hl)			;97bf	96 	. 
	ld b,a			;97c0	47 	G 
	ld d,001h		;97c1	16 01 	. . 
	ld a,004h		;97c3	3e 04 	> . 
	call 0b629h		;97c5	cd 29 b6 	. ) . 
	ld hl,0001eh		;97c8	21 1e 00 	! . . 
	bit 3,(iy+000h)		;97cb	fd cb 00 5e 	. . . ^ 
	jr nz,$+14		;97cf	20 0c 	  . 
	ld hl,0000fh		;97d1	21 0f 00 	! . . 
	bit 5,(iy+000h)		;97d4	fd cb 00 6e 	. . . n 
	jr nz,$+5		;97d8	20 03 	  . 
	ld hl,00007h		;97da	21 07 00 	! . . 
	xor a			;97dd	af 	. 
	call 01fcdh		;97de	cd cd 1f 	. . . 
	ld (iy+002h),a		;97e1	fd 77 02 	. w . 
	ld a,(iy+000h)		;97e4	fd 7e 00 	. ~ . 
	and 0e7h		;97e7	e6 e7 	. . 
	or 080h		;97e9	f6 80 	. . 
	ld (iy+000h),a		;97eb	fd 77 00 	. w . 
	ret			;97ee	c9 	. 
	ld (bc),a			;97ef	02 	. 
	ld b,00eh		;97f0	06 0e 	. . 
	ld b,006h		;97f2	06 06 	. . 
	ld c,006h		;97f4	0e 06 	. . 
	ld (bc),a			;97f6	02 	. 
	ld a,(bc)			;97f7	0a 	. 
	ld c,00ah		;97f8	0e 0a 	. . 
	ld (bc),a			;97fa	02 	. 
	inc c			;97fb	0c 	. 
	ex af,af'			;97fc	08 	. 
	inc b			;97fd	04 	. 
	ex af,af'			;97fe	08 	. 
	ex af,af'			;97ff	08 	. 
	inc b			;9800	04 	. 
	ex af,af'			;9801	08 	. 
	inc c			;9802	0c 	. 
	ex af,af'			;9803	08 	. 
	inc b			;9804	04 	. 
	ex af,af'			;9805	08 	. 
	inc c			;9806	0c 	. 
	ld a,(07273h)		;9807	3a 73 72 	: s r 
	bit 7,a		;980a	cb 7f 	.  
	jr z,$+51		;980c	28 31 	( 1 
	ld ix,0722ch		;980e	dd 21 2c 72 	. ! , r 
	ld b,(ix+001h)		;9812	dd 46 01 	. F . 
	ld c,(ix+002h)		;9815	dd 4e 02 	. N . 
	ld a,(iy+003h)		;9818	fd 7e 03 	. ~ . 
	sub b			;981b	90 	. 
	jr nc,$+4		;981c	30 02 	0 . 
	cpl			;981e	2f 	/ 
	inc a			;981f	3c 	< 
	cp 006h		;9820	fe 06 	. . 
	jr nc,$+29		;9822	30 1b 	0 . 
	ld a,(iy+004h)		;9824	fd 7e 04 	. ~ . 
	sub c			;9827	91 	. 
	jr nc,$+4		;9828	30 02 	0 . 
	cpl			;982a	2f 	/ 
	inc a			;982b	3c 	< 
	cp 006h		;982c	fe 06 	. . 
	jr nc,$+17		;982e	30 0f 	0 . 
	ld de,003e8h		;9830	11 e8 03 	. . . 
	call 0b601h		;9833	cd 01 b6 	. . . 
	ld hl,07273h		;9836	21 73 72 	! s r 
	res 7,(hl)		;9839	cb be 	. . 
	ld a,002h		;983b	3e 02 	> . 
	jr $+3		;983d	18 01 	. . 
	xor a			;983f	af 	. 
	ret			;9840	c9 	. 
	nop			;9841	00 	. 
	ld a,(07272h)		;9842	3a 72 72 	: r r 
	bit 4,a		;9845	cb 67 	. g 
	jr z,$+91		;9847	28 59 	( Y 
	ld a,(072c3h)		;9849	3a c3 72 	: . r 
	bit 7,a		;984c	cb 7f 	.  
	jr nz,$+30		;984e	20 1c 	  . 
	ld a,(0728bh)		;9850	3a 8b 72 	: . r 
	call 01fd0h		;9853	cd d0 1f 	. . . 
	and a			;9856	a7 	. 
	jr z,$+21		;9857	28 13 	( . 
	ld hl,0001eh		;9859	21 1e 00 	! . . 
	xor a			;985c	af 	. 
	call 01fcdh		;985d	cd cd 1f 	. . . 
	ld (0728bh),a		;9860	32 8b 72 	2 . r 
	ld a,(0728ch)		;9863	3a 8c 72 	: . r 
	dec a			;9866	3d 	= 
	ld (0728ch),a		;9867	32 8c 72 	2 . r 
	jr z,$+40		;986a	28 26 	( & 
	ld iy,0728eh		;986c	fd 21 8e 72 	. ! . r 
	ld b,007h		;9870	06 07 	. . 
	bit 7,(iy+004h)		;9872	fd cb 04 7e 	. . . ~ 
	jr z,$+17		;9876	28 0f 	( . 
	bit 6,(iy+004h)		;9878	fd cb 04 76 	. . . v 
	jr nz,$+11		;987c	20 09 	  . 
	push bc			;987e	c5 	. 
	call 09fc8h		;987f	cd c8 9f 	. . . 
	ld l,001h		;9882	2e 01 	. . 
	pop bc			;9884	c1 	. 
	jr nz,$+70		;9885	20 44 	  D 
	ld de,00006h		;9887	11 06 00 	. . . 
	add iy,de		;988a	fd 19 	. . 
	djnz $-26		;988c	10 e4 	. . 
	ld l,000h		;988e	2e 00 	. . 
	jr $+59		;9890	18 39 	. 9 
	ld a,(07272h)		;9892	3a 72 72 	: r r 
	res 4,a		;9895	cb a7 	. . 
	ld (07272h),a		;9897	32 72 72 	2 r r 
	ld a,(0728ah)		;989a	3a 8a 72 	: . r 
	set 4,a		;989d	cb e7 	. . 
	ld (0728ah),a		;989f	32 8a 72 	2 . r 
	jp 0d40bh		;98a2	c3 0b d4 	. . . 
	call 098ceh		;98a5	cd ce 98 	. . . 
	call 09a12h		;98a8	cd 12 9a 	. . . 
	ld l,000h		;98ab	2e 00 	. . 
	ld a,(iy+004h)		;98ad	fd 7e 04 	. ~ . 
	bit 7,a		;98b0	cb 7f 	.  
	jr z,$+16		;98b2	28 0e 	( . 
	bit 6,a		;98b4	cb 77 	. w 
	jr nz,$+12		;98b6	20 0a 	  . 
	bit 7,(iy+000h)		;98b8	fd cb 00 7e 	. . . ~ 
	jr nz,$+6		;98bc	20 04 	  . 
	call 09a2ch		;98be	cd 2c 9a 	. , . 
	ld l,a			;98c1	6f 	o 
	ld a,(0728ch)		;98c2	3a 8c 72 	: . r 
	inc a			;98c5	3c 	< 
	and 007h		;98c6	e6 07 	. . 
	ld (0728ch),a		;98c8	32 8c 72 	2 . r 
	ld a,l			;98cb	7d 	} 
	and a			;98cc	a7 	. 
	ret			;98cd	c9 	. 
	push ix		;98ce	dd e5 	. . 
	ld a,(0728ah)		;98d0	3a 8a 72 	: . r 
	bit 3,a		;98d3	cb 5f 	. _ 
	jr nz,$+83		;98d5	20 51 	  Q 
	ld ix,072b2h		;98d7	dd 21 b2 72 	. ! . r 
	ld a,(ix+003h)		;98db	dd 7e 03 	. ~ . 
	call 01fd0h		;98de	cd d0 1f 	. . . 
	and a			;98e1	a7 	. 
	jr z,$+70		;98e2	28 44 	( D 
	call 09980h		;98e4	cd 80 99 	. . . 
	jr z,$+55		;98e7	28 35 	( 5 
	ld bc,06078h		;98e9	01 78 60 	. x ` 
	call 0992bh		;98ec	cd 2b 99 	. + . 
	jr z,$+7		;98ef	28 05 	( . 
	ld hl,00001h		;98f1	21 01 00 	! . . 
	jr $+33		;98f4	18 1f 	. . 
	call 09962h		;98f6	cd 62 99 	. b . 
	ld a,005h		;98f9	3e 05 	> . 
	ld (iy+005h),a		;98fb	fd 77 05 	. w . 
	call 09980h		;98fe	cd 80 99 	. . . 
	jr z,$+29		;9901	28 1b 	( . 
	ld hl,000d2h		;9903	21 d2 00 	! . . 
	ld a,(0728ah)		;9906	3a 8a 72 	: . r 
	bit 2,a		;9909	cb 57 	. W 
	jr nz,$+5		;990b	20 03 	  . 
	ld hl,0001eh		;990d	21 1e 00 	! . . 
	xor 004h		;9910	ee 04 	. . 
	ld (0728ah),a		;9912	32 8a 72 	2 . r 
	xor a			;9915	af 	. 
	call 01fcdh		;9916	cd cd 1f 	. . . 
	ld (ix+003h),a		;9919	dd 77 03 	. w . 
	jr $+12		;991c	18 0a 	. . 
	ld a,(07272h)		;991e	3a 72 72 	: r r 
	set 0,a		;9921	cb c7 	. . 
	set 7,a		;9923	cb ff 	. . 
	ld (07272h),a		;9925	32 72 72 	2 r r 
	pop ix		;9928	dd e1 	. . 
	ret			;992a	c9 	. 
	push iy		;992b	fd e5 	. . 
	ld iy,0728eh		;992d	fd 21 8e 72 	. ! . r 
	ld bc,00700h		;9931	01 00 07 	. . . 
	ld a,(iy+004h)		;9934	fd 7e 04 	. ~ . 
	bit 7,a		;9937	cb 7f 	.  
	jr z,$+20		;9939	28 12 	( . 
	bit 6,a		;993b	cb 77 	. w 
	jr nz,$+16		;993d	20 0e 	  . 
	ld a,(iy+002h)		;993f	fd 7e 02 	. ~ . 
	sub 060h		;9942	d6 60 	. ` 
	jr nc,$+4		;9944	30 02 	0 . 
	cpl			;9946	2f 	/ 
	inc a			;9947	3c 	< 
	cp 00dh		;9948	fe 0d 	. . 
	jr nc,$+3		;994a	30 01 	0 . 
	inc c			;994c	0c 	. 
	ld de,00006h		;994d	11 06 00 	. . . 
	add iy,de		;9950	fd 19 	. . 
	djnz $-30		;9952	10 e0 	. . 
	ld a,c			;9954	79 	y 
	cp 002h		;9955	fe 02 	. . 
	jr nc,$+5		;9957	30 03 	0 . 
	xor a			;9959	af 	. 
	jr $+4		;995a	18 02 	. . 
	ld a,001h		;995c	3e 01 	> . 
	pop iy		;995e	fd e1 	. . 
	and a			;9960	a7 	. 
	ret			;9961	c9 	. 
	ld a,028h		;9962	3e 28 	> ( 
	ld (iy+000h),a		;9964	fd 77 00 	. w . 
	ld a,081h		;9967	3e 81 	> . 
	ld (iy+004h),a		;9969	fd 77 04 	. w . 
	xor a			;996c	af 	. 
	ld hl,00006h		;996d	21 06 00 	! . . 
	call 01fcdh		;9970	cd cd 1f 	. . . 
	ld (iy+003h),a		;9973	fd 77 03 	. w . 
	ld bc,06078h		;9976	01 78 60 	. x ` 
	ld (iy+002h),b		;9979	fd 70 02 	. p . 
	ld (iy+001h),c		;997c	fd 71 01 	. q . 
	ret			;997f	c9 	. 
	ld iy,0728eh		;9980	fd 21 8e 72 	. ! . r 
	ld l,007h		;9984	2e 07 	. . 
	ld de,00006h		;9986	11 06 00 	. . . 
	bit 7,(iy+004h)		;9989	fd cb 04 7e 	. . . ~ 
	jr z,$+15		;998d	28 0d 	( . 
	add iy,de		;998f	fd 19 	. . 
	dec l			;9991	2d 	- 
	jr nz,$-9		;9992	20 f5 	  . 
	ld a,(0728ah)		;9994	3a 8a 72 	: . r 
	set 3,a		;9997	cb df 	. . 
	ld (0728ah),a		;9999	32 8a 72 	2 . r 
	ld a,l			;999c	7d 	} 
	and a			;999d	a7 	. 
	ret			;999e	c9 	. 
	ld a,(0728ah)		;999f	3a 8a 72 	: . r 
	bit 5,a		;99a2	cb 6f 	. o 
	jr nz,$+23		;99a4	20 15 	  . 
	set 5,a		;99a6	cb ef 	. . 
	ld (0728ah),a		;99a8	32 8a 72 	2 . r 
	ld hl,0003ch		;99ab	21 3c 00 	! < . 
	xor a			;99ae	af 	. 
	call 01fcdh		;99af	cd cd 1f 	. . . 
	ld ix,072b2h		;99b2	dd 21 b2 72 	. ! . r 
	ld (ix+003h),a		;99b6	dd 77 03 	. w . 
	jr $+78		;99b9	18 4c 	. L 
	ld a,(0728bh)		;99bb	3a 8b 72 	: . r 
	call 01fd0h		;99be	cd d0 1f 	. . . 
	and a			;99c1	a7 	. 
	jr z,$+79		;99c2	28 4d 	( M 
	ld a,(0728dh)		;99c4	3a 8d 72 	: . r 
	ld d,a			;99c7	57 	W 
	ld a,(0728ah)		;99c8	3a 8a 72 	: . r 
	set 6,a		;99cb	cb f7 	. . 
	bit 7,a		;99cd	cb 7f 	.  
	jr z,$+21		;99cf	28 13 	( . 
	res 7,a		;99d1	cb bf 	. . 
	ld (0728ah),a		;99d3	32 8a 72 	2 . r 
	inc d			;99d6	14 	. 
	jr nz,$+4		;99d7	20 02 	  . 
	ld d,0ffh		;99d9	16 ff 	. . 
	ld a,d			;99db	7a 	z 
	ld (0728dh),a		;99dc	32 8d 72 	2 . r 
	ld a,(0728ah)		;99df	3a 8a 72 	: . r 
	jr $+7		;99e2	18 05 	. . 
	set 7,a		;99e4	cb ff 	. . 
	ld (0728ah),a		;99e6	32 8a 72 	2 . r 
	ld e,007h		;99e9	1e 07 	. . 
	ld bc,00006h		;99eb	01 06 00 	. . . 
	ld iy,0728eh		;99ee	fd 21 8e 72 	. ! . r 
	ld h,(iy+004h)		;99f2	fd 66 04 	. f . 
	set 5,h		;99f5	cb ec 	. . 
	set 4,h		;99f7	cb e4 	. . 
	bit 7,a		;99f9	cb 7f 	.  
	jr z,$+4		;99fb	28 02 	( . 
	res 4,h		;99fd	cb a4 	. . 
	ld (iy+004h),h		;99ff	fd 74 04 	. t . 
	add iy,bc		;9a02	fd 09 	. . 
	dec e			;9a04	1d 	. 
	jr nz,$-19		;9a05	20 eb 	  . 
	ld hl,0001eh		;9a07	21 1e 00 	! . . 
	xor a			;9a0a	af 	. 
	call 01fcdh		;9a0b	cd cd 1f 	. . . 
	ld (0728bh),a		;9a0e	32 8b 72 	2 . r 
	ret			;9a11	c9 	. 
	ld a,(0728ch)		;9a12	3a 8c 72 	: . r 
	ld c,a			;9a15	4f 	O 
	ld b,000h		;9a16	06 00 	. . 
	ld hl,09a24h		;9a18	21 24 9a 	! $ . 
	add hl,bc			;9a1b	09 	. 
	ld c,(hl)			;9a1c	4e 	N 
	ld iy,0728eh		;9a1d	fd 21 8e 72 	. ! . r 
	add iy,bc		;9a21	fd 09 	. . 
	ret			;9a23	c9 	. 
	nop			;9a24	00 	. 
	ld b,00ch		;9a25	06 0c 	. . 
	ld (de),a			;9a27	12 	. 
	jr $+32		;9a28	18 1e 	. . 
	inc h			;9a2a	24 	$ 
	ld hl,(0e5ddh)		;9a2b	2a dd e5 	* . . 
	ld a,(iy+003h)		;9a2e	fd 7e 03 	. ~ . 
	call 01fd0h		;9a31	cd d0 1f 	. . . 
	and a			;9a34	a7 	. 
	jr z,$+124		;9a35	28 7a 	( z 
	ld a,(iy+000h)		;9a37	fd 7e 00 	. ~ . 
	bit 5,a		;9a3a	cb 6f 	. o 
	jr z,$+20		;9a3c	28 12 	( . 
	bit 3,a		;9a3e	cb 5f 	. _ 
	jr z,$+9		;9a40	28 07 	( . 
	call 09b91h		;9a42	cd 91 9b 	. . . 
	jr nz,$+25		;9a45	20 17 	  . 
	jr $+46		;9a47	18 2c 	. , 
	call 09bbdh		;9a49	cd bd 9b 	. . . 
	jr nz,$+13		;9a4c	20 0b 	  . 
	jr $+39		;9a4e	18 25 	. % 
	bit 4,a		;9a50	cb 67 	. g 
	jr z,$+12		;9a52	28 0a 	( . 
	call 09c76h		;9a54	cd 76 9c 	. v . 
	jr nz,$+30		;9a57	20 1c 	  . 
	call 0a460h		;9a59	cd 60 a4 	. ` . 
	jr $+68		;9a5c	18 42 	. B 
	call 0a1dfh		;9a5e	cd df a1 	. . . 
	jr nz,$+20		;9a61	20 12 	  . 
	call 09cabh		;9a63	cd ab 9c 	. . . 
	jr nz,$+7		;9a66	20 05 	  . 
	call 09e7ch		;9a68	cd 7c 9e 	. | . 
	jr $+10		;9a6b	18 08 	. . 
	call 09ff4h		;9a6d	cd f4 9f 	. . . 
	jr z,$+48		;9a70	28 2e 	( . 
	call 09e3fh		;9a72	cd 3f 9e 	. ? . 
	ld a,(iy+004h)		;9a75	fd 7e 04 	. ~ . 
	and 007h		;9a78	e6 07 	. . 
	call 09d2fh		;9a7a	cd 2f 9d 	. / . 
	jr z,$+35		;9a7d	28 21 	( ! 
	ld a,(iy+004h)		;9a7f	fd 7e 04 	. ~ . 
	and 007h		;9a82	e6 07 	. . 
	dec a			;9a84	3d 	= 
	ld c,a			;9a85	4f 	O 
	ld b,000h		;9a86	06 00 	. . 
	ld hl,09ab5h		;9a88	21 b5 9a 	! . . 
	add hl,bc			;9a8b	09 	. 
	ld b,(hl)			;9a8c	46 	F 
	push bc			;9a8d	c5 	. 
	call 09f29h		;9a8e	cd 29 9f 	. ) . 
	pop bc			;9a91	c1 	. 
	and b			;9a92	a0 	. 
	jr z,$+13		;9a93	28 0b 	( . 
	call 09e7ah		;9a95	cd 7a 9e 	. z . 
	ld a,(iy+004h)		;9a98	fd 7e 04 	. ~ . 
	and 007h		;9a9b	e6 07 	. . 
	call 09d2fh		;9a9d	cd 2f 9d 	. / . 
	call 09ab9h		;9aa0	cd b9 9a 	. . . 
	call 09ae2h		;9aa3	cd e2 9a 	. . . 
	ld a,(iy+004h)		;9aa6	fd 7e 04 	. ~ . 
	and 0c7h		;9aa9	e6 c7 	. . 
	ld (iy+004h),a		;9aab	fd 77 04 	. w . 
	call 09fc8h		;9aae	cd c8 9f 	. . . 
	pop ix		;9ab1	dd e1 	. . 
	and a			;9ab3	a7 	. 
	ret			;9ab4	c9 	. 
	or b			;9ab5	b0 	. 
	ld (hl),b			;9ab6	70 	p 
	ret po			;9ab7	e0 	. 
	ret nc			;9ab8	d0 	. 
	push de			;9ab9	d5 	. 
	push hl			;9aba	e5 	. 
	ld e,(iy+000h)		;9abb	fd 5e 00 	. ^ . 
	ld hl,00006h		;9abe	21 06 00 	! . . 
	bit 5,e		;9ac1	cb 6b 	. k 
	jr nz,$+21		;9ac3	20 13 	  . 
	bit 4,e		;9ac5	cb 63 	. c 
	jr z,$+7		;9ac7	28 05 	( . 
	call 09be2h		;9ac9	cd e2 9b 	. . . 
	jr $+12		;9acc	18 0a 	. . 
	call 09bdah		;9ace	cd da 9b 	. . . 
	bit 3,(iy+004h)		;9ad1	fd cb 04 5e 	. . . ^ 
	jr z,$+3		;9ad5	28 01 	( . 
	add hl,hl			;9ad7	29 	) 
	xor a			;9ad8	af 	. 
	call 01fcdh		;9ad9	cd cd 1f 	. . . 
	ld (iy+003h),a		;9adc	fd 77 03 	. w . 
	pop hl			;9adf	e1 	. 
	pop de			;9ae0	d1 	. 
	ret			;9ae1	c9 	. 
	push ix		;9ae2	dd e5 	. . 
	push iy		;9ae4	fd e5 	. . 
	ld h,(iy+000h)		;9ae6	fd 66 00 	. f . 
	ld d,001h		;9ae9	16 01 	. . 
	bit 6,h		;9aeb	cb 74 	. t 
	jr nz,$+26		;9aed	20 18 	  . 
	ld d,00dh		;9aef	16 0d 	. . 
	bit 5,h		;9af1	cb 6c 	. l 
	jr nz,$+20		;9af3	20 12 	  . 
	call 09b4fh		;9af5	cd 4f 9b 	. O . 
	ld b,(iy+002h)		;9af8	fd 46 02 	. F . 
	ld c,(iy+001h)		;9afb	fd 4e 01 	. N . 
	call 0ac3fh		;9afe	cd 3f ac 	. ? . 
	ld d,a			;9b01	57 	W 
	call 0b173h		;9b02	cd 73 b1 	. s . 
	ld d,019h		;9b05	16 19 	. . 
	ld a,(iy+004h)		;9b07	fd 7e 04 	. ~ . 
	and 007h		;9b0a	e6 07 	. . 
	ld l,000h		;9b0c	2e 00 	. . 
	dec a			;9b0e	3d 	= 
	jr z,$+25		;9b0f	28 17 	( . 
	ld l,002h		;9b11	2e 02 	. . 
	dec a			;9b13	3d 	= 
	jr z,$+20		;9b14	28 12 	( . 
	ld l,004h		;9b16	2e 04 	. . 
	ld b,a			;9b18	47 	G 
	ld a,(iy+001h)		;9b19	fd 7e 01 	. ~ . 
	cp 080h		;9b1c	fe 80 	. . 
	jr nc,$+4		;9b1e	30 02 	0 . 
	ld l,008h		;9b20	2e 08 	. . 
	ld a,b			;9b22	78 	x 
	dec a			;9b23	3d 	= 
	jr z,$+4		;9b24	28 02 	( . 
	inc l			;9b26	2c 	, 
	inc l			;9b27	2c 	, 
	ld c,(iy+005h)		;9b28	fd 4e 05 	. N . 
	bit 7,c		;9b2b	cb 79 	. y 
	jr z,$+6		;9b2d	28 04 	( . 
	res 7,c		;9b2f	cb b9 	. . 
	jr $+5		;9b31	18 03 	. . 
	set 7,c		;9b33	cb f9 	. . 
	inc l			;9b35	2c 	, 
	ld (iy+005h),c		;9b36	fd 71 05 	. q . 
	ld a,d			;9b39	7a 	z 
	add a,l			;9b3a	85 	. 
	ld d,a			;9b3b	57 	W 
	ld a,(0728ch)		;9b3c	3a 8c 72 	: . r 
	add a,005h		;9b3f	c6 05 	. . 
	ld b,(iy+002h)		;9b41	fd 46 02 	. F . 
	ld c,(iy+001h)		;9b44	fd 4e 01 	. N . 
	call 0b629h		;9b47	cd 29 b6 	. ) . 
	pop iy		;9b4a	fd e1 	. . 
	pop ix		;9b4c	dd e1 	. . 
	ret			;9b4e	c9 	. 
	push bc			;9b4f	c5 	. 
	push de			;9b50	d5 	. 
	push hl			;9b51	e5 	. 
	push ix		;9b52	dd e5 	. . 
	ld a,(iy+000h)		;9b54	fd 7e 00 	. ~ . 
	bit 0,a		;9b57	cb 47 	. G 
	jr nz,$+42		;9b59	20 28 	  ( 
	bit 5,a		;9b5b	cb 6f 	. o 
	jr nz,$+38		;9b5d	20 24 	  $ 
	ld a,(iy+004h)		;9b5f	fd 7e 04 	. ~ . 
	and 007h		;9b62	e6 07 	. . 
	dec a			;9b64	3d 	= 
	cp 004h		;9b65	fe 04 	. . 
	jr nc,$+28		;9b67	30 1a 	0 . 
	ld hl,09b89h		;9b69	21 89 9b 	! . . 
	add a,a			;9b6c	87 	. 
	ld c,a			;9b6d	4f 	O 
	ld b,000h		;9b6e	06 00 	. . 
	add hl,bc			;9b70	09 	. 
	ld e,(hl)			;9b71	5e 	^ 
	inc hl			;9b72	23 	# 
	ld d,(hl)			;9b73	56 	V 
	push de			;9b74	d5 	. 
	pop ix		;9b75	dd e1 	. . 
	ld b,(iy+002h)		;9b77	fd 46 02 	. F . 
	ld c,(iy+001h)		;9b7a	fd 4e 01 	. N . 
	ld de,09b83h		;9b7d	11 83 9b 	. . . 
	push de			;9b80	d5 	. 
	jp (ix)		;9b81	dd e9 	. . 
	pop ix		;9b83	dd e1 	. . 
	pop hl			;9b85	e1 	. 
	pop de			;9b86	d1 	. 
	pop bc			;9b87	c1 	. 
	ret			;9b88	c9 	. 
	jp m,09db2h		;9b89	fa b2 9d 	. . . 
	or e			;9b8c	b3 	. 
	ccf			;9b8d	3f 	? 
	or h			;9b8e	b4 	. 
	jp (hl)			;9b8f	e9 	. 
	or h			;9b90	b4 	. 
	call 09ba8h		;9b91	cd a8 9b 	. . . 
	ld b,000h		;9b94	06 00 	. . 
	jr nz,$+15		;9b96	20 0d 	  . 
	ld a,(iy+000h)		;9b98	fd 7e 00 	. ~ . 
	res 5,a		;9b9b	cb af 	. . 
	set 6,a		;9b9d	cb f7 	. . 
	and 0f8h		;9b9f	e6 f8 	. . 
	ld (iy+000h),a		;9ba1	fd 77 00 	. w . 
	inc b			;9ba4	04 	. 
	ld a,b			;9ba5	78 	x 
	and a			;9ba6	a7 	. 
	ret			;9ba7	c9 	. 
	ld a,(iy+005h)		;9ba8	fd 7e 05 	. ~ . 
	dec a			;9bab	3d 	= 
	ld (iy+005h),a		;9bac	fd 77 05 	. w . 
	and 03fh		;9baf	e6 3f 	. ? 
	ret			;9bb1	c9 	. 
	ld c,a			;9bb2	4f 	O 
	ld a,(iy+005h)		;9bb3	fd 7e 05 	. ~ . 
	and 0c0h		;9bb6	e6 c0 	. . 
	or c			;9bb8	b1 	. 
	ld (iy+005h),a		;9bb9	fd 77 05 	. w . 
	ret			;9bbc	c9 	. 
	ld b,000h		;9bbd	06 00 	. . 
	call 09ba8h		;9bbf	cd a8 9b 	. . . 
	jr nz,$+21		;9bc2	20 13 	  . 
	ld a,(iy+000h)		;9bc4	fd 7e 00 	. ~ . 
	and 0f8h		;9bc7	e6 f8 	. . 
	res 5,a		;9bc9	cb af 	. . 
	set 4,a		;9bcb	cb e7 	. . 
	ld (iy+000h),a		;9bcd	fd 77 00 	. w . 
	call 09be2h		;9bd0	cd e2 9b 	. . . 
	call 09bb2h		;9bd3	cd b2 9b 	. . . 
	inc b			;9bd6	04 	. 
	ld a,b			;9bd7	78 	x 
	or a			;9bd8	b7 	. 
	ret			;9bd9	c9 	. 
	push bc			;9bda	c5 	. 
	push de			;9bdb	d5 	. 
	push ix		;9bdc	dd e5 	. . 
	ld d,000h		;9bde	16 00 	. . 
	jr $+8		;9be0	18 06 	. . 
	push bc			;9be2	c5 	. 
	push de			;9be3	d5 	. 
	push ix		;9be4	dd e5 	. . 
	ld d,001h		;9be6	16 01 	. . 
	ld a,(07271h)		;9be8	3a 71 72 	: q r 
	dec a			;9beb	3d 	= 
	ld c,a			;9bec	4f 	O 
	ld b,000h		;9bed	06 00 	. . 
	ld ix,09d1ah		;9bef	dd 21 1a 9d 	. ! . . 
	add ix,bc		;9bf3	dd 09 	. . 
	ld c,(ix+000h)		;9bf5	dd 4e 00 	. N . 
	ld hl,07274h		;9bf8	21 74 72 	! t r 
	ld a,(0726eh)		;9bfb	3a 6e 72 	: n r 
	and 003h		;9bfe	e6 03 	. . 
	cp 003h		;9c00	fe 03 	. . 
	jr nz,$+3		;9c02	20 01 	  . 
	inc hl			;9c04	23 	# 
	ld a,(hl)			;9c05	7e 	~ 
	dec a			;9c06	3d 	= 
	add a,c			;9c07	81 	. 
	ld c,a			;9c08	4f 	O 
	ld a,(0728ah)		;9c09	3a 8a 72 	: . r 
	bit 4,a		;9c0c	cb 67 	. g 
	jr z,$+4		;9c0e	28 02 	( . 
	inc c			;9c10	0c 	. 
	inc c			;9c11	0c 	. 
	ld a,c			;9c12	79 	y 
	cp 00fh		;9c13	fe 0f 	. . 
	jr c,$+4		;9c15	38 02 	8 . 
	ld a,00fh		;9c17	3e 0f 	> . 
	add a,a			;9c19	87 	. 
	ld c,a			;9c1a	4f 	O 
	ld ix,09c56h		;9c1b	dd 21 56 9c 	. ! V . 
	ld a,d			;9c1f	7a 	z 
	and a			;9c20	a7 	. 
	jr z,$+6		;9c21	28 04 	( . 
	ld ix,09c36h		;9c23	dd 21 36 9c 	. ! 6 . 
	add ix,bc		;9c27	dd 09 	. . 
	ld l,(ix+000h)		;9c29	dd 6e 00 	. n . 
	ld h,000h		;9c2c	26 00 	& . 
	ld a,(ix+001h)		;9c2e	dd 7e 01 	. ~ . 
	pop ix		;9c31	dd e1 	. . 
	pop de			;9c33	d1 	. 
	pop bc			;9c34	c1 	. 
	ret			;9c35	c9 	. 
	dec c			;9c36	0d 	. 
	add hl,bc			;9c37	09 	. 
	dec c			;9c38	0d 	. 
	add hl,bc			;9c39	09 	. 
	dec c			;9c3a	0d 	. 
	add hl,bc			;9c3b	09 	. 
	ld a,(bc)			;9c3c	0a 	. 
	inc c			;9c3d	0c 	. 
	ld a,(bc)			;9c3e	0a 	. 
	inc c			;9c3f	0c 	. 
	ld a,(bc)			;9c40	0a 	. 
	inc c			;9c41	0c 	. 
	ex af,af'			;9c42	08 	. 
	rrca			;9c43	0f 	. 
	ex af,af'			;9c44	08 	. 
	rrca			;9c45	0f 	. 
	ld b,014h		;9c46	06 14 	. . 
	ld b,014h		;9c48	06 14 	. . 
	dec b			;9c4a	05 	. 
	jr $+7		;9c4b	18 05 	. . 
	jr $+7		;9c4d	18 05 	. . 
	jr $+6		;9c4f	18 04 	. . 
	ld e,004h		;9c51	1e 04 	. . 
	ld e,004h		;9c53	1e 04 	. . 
	ld e,008h		;9c55	1e 08 	. . 
	ld bc,00108h		;9c57	01 08 01 	. . . 
	ex af,af'			;9c5a	08 	. 
	ld bc,00106h		;9c5b	01 06 01 	. . . 
	ld b,001h		;9c5e	06 01 	. . 
	ld b,001h		;9c60	06 01 	. . 
	dec b			;9c62	05 	. 
	ld bc,00105h		;9c63	01 05 01 	. . . 
	dec b			;9c66	05 	. 
	ld bc,00105h		;9c67	01 05 01 	. . . 
	inc b			;9c6a	04 	. 
	ld bc,00104h		;9c6b	01 04 01 	. . . 
	inc b			;9c6e	04 	. 
	ld bc,00104h		;9c6f	01 04 01 	. . . 
	inc b			;9c72	04 	. 
	ld bc,00104h		;9c73	01 04 01 	. . . 
	ld b,000h		;9c76	06 00 	. . 
	ld a,(iy+005h)		;9c78	fd 7e 05 	. ~ . 
	and 03fh		;9c7b	e6 3f 	. ? 
	jr z,$+7		;9c7d	28 05 	( . 
	call 09ba8h		;9c7f	cd a8 9b 	. . . 
	jr nz,$+38		;9c82	20 24 	  $ 
	ld a,(iy+002h)		;9c84	fd 7e 02 	. ~ . 
	and 00fh		;9c87	e6 0f 	. . 
	jr nz,$+31		;9c89	20 1d 	  . 
	ld a,(iy+001h)		;9c8b	fd 7e 01 	. ~ . 
	and 00fh		;9c8e	e6 0f 	. . 
	cp 008h		;9c90	fe 08 	. . 
	jr nz,$+22		;9c92	20 14 	  . 
	ld a,(iy+000h)		;9c94	fd 7e 00 	. ~ . 
	and 0f8h		;9c97	e6 f8 	. . 
	res 4,a		;9c99	cb a7 	. . 
	set 5,a		;9c9b	cb ef 	. . 
	set 3,a		;9c9d	cb df 	. . 
	ld (iy+000h),a		;9c9f	fd 77 00 	. w . 
	ld a,00ah		;9ca2	3e 0a 	> . 
	call 09bb2h		;9ca4	cd b2 9b 	. . . 
	inc b			;9ca7	04 	. 
	ld a,b			;9ca8	78 	x 
	and a			;9ca9	a7 	. 
	ret			;9caa	c9 	. 
	ld b,(iy+000h)		;9cab	fd 46 00 	. F . 
	bit 5,(iy+004h)		;9cae	fd cb 04 6e 	. . . n 
	jr nz,$+8		;9cb2	20 06 	  . 
	bit 2,b		;9cb4	cb 50 	. P 
	jr nz,$+30		;9cb6	20 1c 	  . 
	jr $+34		;9cb8	18 20 	.   
	call 09ce0h		;9cba	cd e0 9c 	. . . 
	ld e,a			;9cbd	5f 	_ 
	ld a,(0728dh)		;9cbe	3a 8d 72 	: . r 
	rra			;9cc1	1f 	. 
	rra			;9cc2	1f 	. 
	rra			;9cc3	1f 	. 
	rra			;9cc4	1f 	. 
	rra			;9cc5	1f 	. 
	and 007h		;9cc6	e6 07 	. . 
	add a,e			;9cc8	83 	. 
	ld e,a			;9cc9	5f 	_ 
	call 01ffdh		;9cca	cd fd 1f 	. . . 
	and 00fh		;9ccd	e6 0f 	. . 
	res 2,b		;9ccf	cb 90 	. . 
	cp e			;9cd1	bb 	. 
	jr nc,$+8		;9cd2	30 06 	0 . 
	set 2,b		;9cd4	cb d0 	. . 
	res 0,b		;9cd6	cb 80 	. . 
	res 1,b		;9cd8	cb 88 	. . 
	ld (iy+000h),b		;9cda	fd 70 00 	. p . 
	bit 2,b		;9cdd	cb 50 	. P 
	ret			;9cdf	c9 	. 
	push de			;9ce0	d5 	. 
	push hl			;9ce1	e5 	. 
	ld a,(07271h)		;9ce2	3a 71 72 	: q r 
	dec a			;9ce5	3d 	= 
	ld e,a			;9ce6	5f 	_ 
	ld d,000h		;9ce7	16 00 	. . 
	ld hl,09d1ah		;9ce9	21 1a 9d 	! . . 
	add hl,de			;9cec	19 	. 
	ld e,(hl)			;9ced	5e 	^ 
	ld hl,07274h		;9cee	21 74 72 	! t r 
	ld a,(0726eh)		;9cf1	3a 6e 72 	: n r 
	and 003h		;9cf4	e6 03 	. . 
	cp 003h		;9cf6	fe 03 	. . 
	jr nz,$+3		;9cf8	20 01 	  . 
	inc hl			;9cfa	23 	# 
	ld a,(hl)			;9cfb	7e 	~ 
	dec a			;9cfc	3d 	= 
	add a,e			;9cfd	83 	. 
	ld e,a			;9cfe	5f 	_ 
	ld a,(0728ah)		;9cff	3a 8a 72 	: . r 
	bit 4,a		;9d02	cb 67 	. g 
	jr z,$+4		;9d04	28 02 	( . 
	inc e			;9d06	1c 	. 
	inc e			;9d07	1c 	. 
	ld a,e			;9d08	7b 	{ 
	cp 00fh		;9d09	fe 0f 	. . 
	jr c,$+4		;9d0b	38 02 	8 . 
	ld a,00fh		;9d0d	3e 0f 	> . 
	ld e,a			;9d0f	5f 	_ 
	ld d,000h		;9d10	16 00 	. . 
	ld hl,09d1eh		;9d12	21 1e 9d 	! . . 
	add hl,de			;9d15	19 	. 
	ld a,(hl)			;9d16	7e 	~ 
	pop hl			;9d17	e1 	. 
	pop de			;9d18	d1 	. 
	ret			;9d19	c9 	. 
	nop			;9d1a	00 	. 
	inc bc			;9d1b	03 	. 
	dec b			;9d1c	05 	. 
	rlca			;9d1d	07 	. 
	ex af,af'			;9d1e	08 	. 
	ex af,af'			;9d1f	08 	. 
	add hl,bc			;9d20	09 	. 
	add hl,bc			;9d21	09 	. 
	ld a,(bc)			;9d22	0a 	. 
	ld a,(bc)			;9d23	0a 	. 
	dec bc			;9d24	0b 	. 
	dec bc			;9d25	0b 	. 
	inc c			;9d26	0c 	. 
	inc c			;9d27	0c 	. 
	dec c			;9d28	0d 	. 
	dec c			;9d29	0d 	. 
	ld c,00eh		;9d2a	0e 0e 	. . 
	ld c,00eh		;9d2c	0e 0e 	. . 
	ld c,04fh		;9d2e	0e 4f 	. O 
	xor a			;9d30	af 	. 
	ld h,(iy+000h)		;9d31	fd 66 00 	. f . 
	bit 0,h		;9d34	cb 44 	. D 
	jr nz,$+103		;9d36	20 65 	  e 
	bit 5,h		;9d38	cb 6c 	. l 
	jr nz,$+99		;9d3a	20 61 	  a 
	push bc			;9d3c	c5 	. 
	ld b,(iy+002h)		;9d3d	fd 46 02 	. F . 
	ld c,(iy+001h)		;9d40	fd 4e 01 	. N . 
	call 09e07h		;9d43	cd 07 9e 	. . . 
	pop bc			;9d46	c1 	. 
	jr nz,$+86		;9d47	20 54 	  T 
	dec c			;9d49	0d 	. 
	ld a,c			;9d4a	79 	y 
	cp 004h		;9d4b	fe 04 	. . 
	ld a,000h		;9d4d	3e 00 	> . 
	jr nc,$+78		;9d4f	30 4c 	0 L 
	ld a,c			;9d51	79 	y 
	rlca			;9d52	07 	. 
	ld c,a			;9d53	4f 	O 
	ld b,000h		;9d54	06 00 	. . 
	ld hl,09d9fh		;9d56	21 9f 9d 	! . . 
	add hl,bc			;9d59	09 	. 
	ld e,(hl)			;9d5a	5e 	^ 
	inc hl			;9d5b	23 	# 
	ld d,(hl)			;9d5c	56 	V 
	ex de,hl			;9d5d	eb 	. 
	ld b,(iy+002h)		;9d5e	fd 46 02 	. F . 
	ld c,(iy+001h)		;9d61	fd 4e 01 	. N . 
	ld e,004h		;9d64	1e 04 	. . 
	jp (hl)			;9d66	e9 	. 
	ld a,c			;9d67	79 	y 
	add a,e			;9d68	83 	. 
	ld c,a			;9d69	4f 	O 
	jr $+15		;9d6a	18 0d 	. . 
	ld a,c			;9d6c	79 	y 
	sub e			;9d6d	93 	. 
	ld c,a			;9d6e	4f 	O 
	jr $+10		;9d6f	18 08 	. . 
	ld a,b			;9d71	78 	x 
	sub e			;9d72	93 	. 
	ld b,a			;9d73	47 	G 
	jr $+5		;9d74	18 03 	. . 
	ld a,b			;9d76	78 	x 
	add a,e			;9d77	83 	. 
	ld b,a			;9d78	47 	G 
	push hl			;9d79	e5 	. 
	push bc			;9d7a	c5 	. 
	push iy		;9d7b	fd e5 	. . 
	pop hl			;9d7d	e1 	. 
	ld bc,072b8h		;9d7e	01 b8 72 	. . r 
	and a			;9d81	a7 	. 
	sbc hl,bc		;9d82	ed 42 	. B 
	pop bc			;9d84	c1 	. 
	pop hl			;9d85	e1 	. 
	jr nc,$+12		;9d86	30 0a 	0 . 
	ld a,(iy+004h)		;9d88	fd 7e 04 	. ~ . 
	and 007h		;9d8b	e6 07 	. . 
	call 09da7h		;9d8d	cd a7 9d 	. . . 
	jr nz,$+13		;9d90	20 0b 	  . 
	call 09e07h		;9d92	cd 07 9e 	. . . 
	jr nz,$+8		;9d95	20 06 	  . 
	ld (iy+002h),b		;9d97	fd 70 02 	. p . 
	ld (iy+001h),c		;9d9a	fd 71 01 	. q . 
	and a			;9d9d	a7 	. 
	ret			;9d9e	c9 	. 
	ld h,a			;9d9f	67 	g 
	sbc a,l			;9da0	9d 	. 
	ld l,h			;9da1	6c 	l 
	sbc a,l			;9da2	9d 	. 
	ld (hl),c			;9da3	71 	q 
	sbc a,l			;9da4	9d 	. 
	halt			;9da5	76 	v 
	sbc a,l			;9da6	9d 	. 
	push bc			;9da7	c5 	. 
	push ix		;9da8	dd e5 	. . 
	cp 003h		;9daa	fe 03 	. . 
	jr c,$+85		;9dac	38 53 	8 S 
	ld c,a			;9dae	4f 	O 
	ld ix,0728eh		;9daf	dd 21 8e 72 	. ! . r 
	ld hl,00007h		;9db3	21 07 00 	! . . 
	bit 7,(ix+004h)		;9db6	dd cb 04 7e 	. . . ~ 
	jr z,$+54		;9dba	28 34 	( 4 
	bit 6,(ix+004h)		;9dbc	dd cb 04 76 	. . . v 
	jr nz,$+48		;9dc0	20 2e 	  . 
	ld a,(ix+002h)		;9dc2	dd 7e 02 	. ~ . 
	bit 2,c		;9dc5	cb 51 	. Q 
	jr nz,$+14		;9dc7	20 0c 	  . 
	cp b			;9dc9	b8 	. 
	jr z,$+4		;9dca	28 02 	( . 
	jr nc,$+36		;9dcc	30 22 	0 " 
	add a,00ch		;9dce	c6 0c 	. . 
	cp b			;9dd0	b8 	. 
	jr c,$+31		;9dd1	38 1d 	8 . 
	jr $+10		;9dd3	18 08 	. . 
	cp b			;9dd5	b8 	. 
	jr c,$+26		;9dd6	38 18 	8 . 
	sub 00dh		;9dd8	d6 0d 	. . 
	cp b			;9dda	b8 	. 
	jr nc,$+21		;9ddb	30 13 	0 . 
	inc h			;9ddd	24 	$ 
	ld a,h			;9dde	7c 	| 
	cp 001h		;9ddf	fe 01 	. . 
	jr nz,$+15		;9de1	20 0d 	  . 
	push hl			;9de3	e5 	. 
	push iy		;9de4	fd e5 	. . 
	pop de			;9de6	d1 	. 
	push ix		;9de7	dd e5 	. . 
	pop hl			;9de9	e1 	. 
	and a			;9dea	a7 	. 
	sbc hl,de		;9deb	ed 52 	. R 
	pop hl			;9ded	e1 	. 
	jr nc,$+19		;9dee	30 11 	0 . 
	ld de,00006h		;9df0	11 06 00 	. . . 
	add ix,de		;9df3	dd 19 	. . 
	dec l			;9df5	2d 	- 
	jr nz,$-64		;9df6	20 be 	  . 
	ld a,h			;9df8	7c 	| 
	cp 002h		;9df9	fe 02 	. . 
	jr c,$+6		;9dfb	38 04 	8 . 
	ld a,0ffh		;9dfd	3e ff 	> . 
	jr $+3		;9dff	18 01 	. . 
	xor a			;9e01	af 	. 
	pop ix		;9e02	dd e1 	. . 
	pop bc			;9e04	c1 	. 
	and a			;9e05	a7 	. 
	ret			;9e06	c9 	. 
	push bc			;9e07	c5 	. 
	ld a,(iy+004h)		;9e08	fd 7e 04 	. ~ . 
	and 007h		;9e0b	e6 07 	. . 
	ld d,a			;9e0d	57 	W 
	ld a,003h		;9e0e	3e 03 	> . 
	bit 4,(iy+000h)		;9e10	fd cb 00 66 	. . . f 
	jr z,$+3		;9e14	28 01 	( . 
	dec a			;9e16	3d 	= 
	ld e,a			;9e17	5f 	_ 
	ld a,d			;9e18	7a 	z 
	cp 003h		;9e19	fe 03 	. . 
	ld a,e			;9e1b	7b 	{ 
	jr nc,$+21		;9e1c	30 13 	0 . 
	call 0aee1h		;9e1e	cd e1 ae 	. . . 
	cp 002h		;9e21	fe 02 	. . 
	jr nc,$+22		;9e23	30 14 	0 . 
	ld l,000h		;9e25	2e 00 	. . 
	cp 001h		;9e27	fe 01 	. . 
	jr nz,$+18		;9e29	20 10 	  . 
	set 3,(iy+004h)		;9e2b	fd cb 04 de 	. . . . 
	jr $+12		;9e2f	18 0a 	. . 
	call 0b12dh		;9e31	cd 2d b1 	. - . 
	ld l,000h		;9e34	2e 00 	. . 
	and a			;9e36	a7 	. 
	jr z,$+4		;9e37	28 02 	( . 
	ld l,001h		;9e39	2e 01 	. . 
	pop bc			;9e3b	c1 	. 
	ld a,l			;9e3c	7d 	} 
	and a			;9e3d	a7 	. 
	ret			;9e3e	c9 	. 
	set 0,(iy+000h)		;9e3f	fd cb 00 c6 	. . . . 
	bit 4,(iy+004h)		;9e43	fd cb 04 66 	. . . f 
	jr z,$+46		;9e47	28 2c 	( , 
	call 0a527h		;9e49	cd 27 a5 	. ' . 
	jr z,$+8		;9e4c	28 06 	( . 
	bit 3,(iy+004h)		;9e4e	fd cb 04 5e 	. . . ^ 
	jr z,$+35		;9e52	28 21 	( ! 
	call 09ce0h		;9e54	cd e0 9c 	. . . 
	and 00fh		;9e57	e6 0f 	. . 
	ld b,a			;9e59	47 	G 
	call 01ffdh		;9e5a	cd fd 1f 	. . . 
	and 00fh		;9e5d	e6 0f 	. . 
	cp b			;9e5f	b8 	. 
	jr nc,$+21		;9e60	30 13 	0 . 
	ld a,(iy+000h)		;9e62	fd 7e 00 	. ~ . 
	and 0f8h		;9e65	e6 f8 	. . 
	res 6,a		;9e67	cb b7 	. . 
	set 5,a		;9e69	cb ef 	. . 
	res 3,a		;9e6b	cb 9f 	. . 
	ld (iy+000h),a		;9e6d	fd 77 00 	. w . 
	ld a,00ah		;9e70	3e 0a 	> . 
	call 09bb2h		;9e72	cd b2 9b 	. . . 
	res 3,(iy+004h)		;9e75	fd cb 04 9e 	. . . . 
	ret			;9e79	c9 	. 
	jr $+67		;9e7a	18 41 	. A 
	bit 4,(iy+004h)		;9e7c	fd cb 04 66 	. . . f 
	jr nz,$+42		;9e80	20 28 	  ( 
	bit 0,(iy+000h)		;9e82	fd cb 00 46 	. . . F 
	jp nz,09f10h		;9e86	c2 10 9f 	. . . 
	ld a,(iy+004h)		;9e89	fd 7e 04 	. ~ . 
	and 007h		;9e8c	e6 07 	. . 
	dec a			;9e8e	3d 	= 
	cp 004h		;9e8f	fe 04 	. . 
	jr nc,$+25		;9e91	30 17 	0 . 
	ld hl,09f25h		;9e93	21 25 9f 	! % . 
	ld c,a			;9e96	4f 	O 
	ld b,000h		;9e97	06 00 	. . 
	add hl,bc			;9e99	09 	. 
	ld b,(hl)			;9e9a	46 	F 
	push bc			;9e9b	c5 	. 
	call 09f29h		;9e9c	cd 29 9f 	. ) . 
	pop bc			;9e9f	c1 	. 
	and a			;9ea0	a7 	. 
	jr z,$+9		;9ea1	28 07 	( . 
	ld c,a			;9ea3	4f 	O 
	and b			;9ea4	a0 	. 
	jr nz,$+107		;9ea5	20 69 	  i 
	ld a,c			;9ea7	79 	y 
	jr $+21		;9ea8	18 13 	. . 
	set 0,(iy+000h)		;9eaa	fd cb 00 c6 	. . . . 
	call 01ffdh		;9eae	cd fd 1f 	. . . 
	and 00fh		;9eb1	e6 0f 	. . 
	cp 008h		;9eb3	fe 08 	. . 
	jr c,$+91		;9eb5	38 59 	8 Y 
	call 09f29h		;9eb7	cd 29 9f 	. ) . 
	and a			;9eba	a7 	. 
	jr z,$+85		;9ebb	28 53 	( S 
	ld ix,09f15h		;9ebd	dd 21 15 9f 	. ! . . 
	ld c,004h		;9ec1	0e 04 	. . 
	ld e,(ix+001h)		;9ec3	dd 5e 01 	. ^ . 
	cp (ix+000h)		;9ec6	dd be 00 	. . . 
	jr z,$+58		;9ec9	28 38 	( 8 
	inc ix		;9ecb	dd 23 	. # 
	inc ix		;9ecd	dd 23 	. # 
	dec c			;9ecf	0d 	. 
	jr nz,$-13		;9ed0	20 f1 	  . 
	ld b,a			;9ed2	47 	G 
	call 01ffdh		;9ed3	cd fd 1f 	. . . 
	and 003h		;9ed6	e6 03 	. . 
	rlca			;9ed8	07 	. 
	ld hl,09f1dh		;9ed9	21 1d 9f 	! . . 
	ld e,a			;9edc	5f 	_ 
	ld d,000h		;9edd	16 00 	. . 
	add hl,de			;9edf	19 	. 
	ld e,(hl)			;9ee0	5e 	^ 
	inc hl			;9ee1	23 	# 
	ld d,(hl)			;9ee2	56 	V 
	ex de,hl			;9ee3	eb 	. 
	jp (hl)			;9ee4	e9 	. 
	ld e,003h		;9ee5	1e 03 	. . 
	bit 4,b		;9ee7	cb 60 	. ` 
	jr nz,$+26		;9ee9	20 18 	  . 
	jr $-24		;9eeb	18 e6 	. . 
	ld e,004h		;9eed	1e 04 	. . 
	bit 5,b		;9eef	cb 68 	. h 
	jr nz,$+18		;9ef1	20 10 	  . 
	jr $-32		;9ef3	18 de 	. . 
	ld e,001h		;9ef5	1e 01 	. . 
	bit 6,b		;9ef7	cb 70 	. p 
	jr nz,$+10		;9ef9	20 08 	  . 
	jr $-40		;9efb	18 d6 	. . 
	ld e,002h		;9efd	1e 02 	. . 
	bit 7,b		;9eff	cb 78 	. x 
	jr z,$-46		;9f01	28 d0 	( . 
	res 0,(iy+000h)		;9f03	fd cb 00 86 	. . . . 
	ld a,(iy+004h)		;9f07	fd 7e 04 	. ~ . 
	and 0f8h		;9f0a	e6 f8 	. . 
	or e			;9f0c	b3 	. 
	ld (iy+004h),a		;9f0d	fd 77 04 	. w . 
	bit 0,(iy+000h)		;9f10	fd cb 00 46 	. . . F 
	ret			;9f14	c9 	. 
	djnz $+5		;9f15	10 03 	. . 
	jr nz,$+6		;9f17	20 04 	  . 
	ld b,b			;9f19	40 	@ 
	ld bc,00280h		;9f1a	01 80 02 	. . . 
	push hl			;9f1d	e5 	. 
	sbc a,(hl)			;9f1e	9e 	. 
	defb 0edh;next byte illegal after ed		;9f1f	ed 	. 
	sbc a,(hl)			;9f20	9e 	. 
	push af			;9f21	f5 	. 
	sbc a,(hl)			;9f22	9e 	. 
	sbc a,(iy+040h)		;9f23	fd 9e 40 	. . @ 
	add a,b			;9f26	80 	. 
	djnz $+34		;9f27	10 20 	.   
	push ix		;9f29	dd e5 	. . 
	ld b,(iy+002h)		;9f2b	fd 46 02 	. F . 
	ld c,(iy+001h)		;9f2e	fd 4e 01 	. N . 
	call 0ac3fh		;9f31	cd 3f ac 	. ? . 
	ld c,a			;9f34	4f 	O 
	ld hl,09fb3h		;9f35	21 b3 9f 	! . . 
	ld a,(iy+001h)		;9f38	fd 7e 01 	. ~ . 
	rlca			;9f3b	07 	. 
	rlca			;9f3c	07 	. 
	rlca			;9f3d	07 	. 
	rlca			;9f3e	07 	. 
	and 0f0h		;9f3f	e6 f0 	. . 
	ld b,a			;9f41	47 	G 
	ld a,(iy+002h)		;9f42	fd 7e 02 	. ~ . 
	and 00fh		;9f45	e6 0f 	. . 
	or b			;9f47	b0 	. 
	ld e,007h		;9f48	1e 07 	. . 
	cp (hl)			;9f4a	be 	. 
	jr z,$+10		;9f4b	28 08 	( . 
	inc hl			;9f4d	23 	# 
	inc hl			;9f4e	23 	# 
	inc hl			;9f4f	23 	# 
	dec e			;9f50	1d 	. 
	jr nz,$-7		;9f51	20 f7 	  . 
	jr $+77		;9f53	18 4b 	. K 
	xor a			;9f55	af 	. 
	inc hl			;9f56	23 	# 
	ld e,(hl)			;9f57	5e 	^ 
	inc hl			;9f58	23 	# 
	ld d,(hl)			;9f59	56 	V 
	push ix		;9f5a	dd e5 	. . 
	push de			;9f5c	d5 	. 
	pop ix		;9f5d	dd e1 	. . 
	pop hl			;9f5f	e1 	. 
	jp (ix)		;9f60	dd e9 	. . 
	bit 1,(hl)		;9f62	cb 4e 	. N 
	jr z,$+8		;9f64	28 06 	( . 
	bit 3,(hl)		;9f66	cb 5e 	. ^ 
	jr z,$+4		;9f68	28 02 	( . 
	set 6,a		;9f6a	cb f7 	. . 
	dec hl			;9f6c	2b 	+ 
	bit 0,(hl)		;9f6d	cb 46 	. F 
	jr z,$+64		;9f6f	28 3e 	( > 
	bit 2,(hl)		;9f71	cb 56 	. V 
	jr z,$+60		;9f73	28 3a 	( : 
	set 7,a		;9f75	cb ff 	. . 
	jr $+56		;9f77	18 36 	. 6 
	ld a,(hl)			;9f79	7e 	~ 
	and 0f0h		;9f7a	e6 f0 	. . 
	jr $+51		;9f7c	18 31 	. 1 
	ld a,0c0h		;9f7e	3e c0 	> . 
	jr $+47		;9f80	18 2d 	. - 
	bit 2,(hl)		;9f82	cb 56 	. V 
	jr z,$+8		;9f84	28 06 	( . 
	bit 3,(hl)		;9f86	cb 5e 	. ^ 
	jr z,$+4		;9f88	28 02 	( . 
	set 5,a		;9f8a	cb ef 	. . 
	ld bc,0fff0h		;9f8c	01 f0 ff 	. . . 
	add hl,bc			;9f8f	09 	. 
	bit 0,(hl)		;9f90	cb 46 	. F 
	jr z,$+29		;9f92	28 1b 	( . 
	bit 1,(hl)		;9f94	cb 4e 	. N 
	jr z,$+25		;9f96	28 17 	( . 
	set 4,a		;9f98	cb e7 	. . 
	jr $+21		;9f9a	18 13 	. . 
	ld a,030h		;9f9c	3e 30 	> 0 
	jr $+17		;9f9e	18 0f 	. . 
	ld a,(hl)			;9fa0	7e 	~ 
	and 0f0h		;9fa1	e6 f0 	. . 
	push af			;9fa3	f5 	. 
	ld a,c			;9fa4	79 	y 
	call 0abb7h		;9fa5	cd b7 ab 	. . . 
	ld (iy+002h),b		;9fa8	fd 70 02 	. p . 
	ld (iy+001h),c		;9fab	fd 71 01 	. q . 
	pop af			;9fae	f1 	. 
	and a			;9faf	a7 	. 
	pop ix		;9fb0	dd e1 	. . 
	ret			;9fb2	c9 	. 
	nop			;9fb3	00 	. 
	ld h,d			;9fb4	62 	b 
	sbc a,a			;9fb5	9f 	. 
	ld b,b			;9fb6	40 	@ 
	ld a,(hl)			;9fb7	7e 	~ 
	sbc a,a			;9fb8	9f 	. 
	add a,b			;9fb9	80 	. 
	ld a,c			;9fba	79 	y 
	sbc a,a			;9fbb	9f 	. 
	ret nz			;9fbc	c0 	. 
	ld a,(hl)			;9fbd	7e 	~ 
	sbc a,a			;9fbe	9f 	. 
	adc a,b			;9fbf	88 	. 
	add a,d			;9fc0	82 	. 
	sbc a,a			;9fc1	9f 	. 
	add a,h			;9fc2	84 	. 
	sbc a,h			;9fc3	9c 	. 
	sbc a,a			;9fc4	9f 	. 
	adc a,h			;9fc5	8c 	. 
	sbc a,h			;9fc6	9c 	. 
	sbc a,a			;9fc7	9f 	. 
	push iy		;9fc8	fd e5 	. . 
	ld b,(iy+002h)		;9fca	fd 46 02 	. F . 
	ld a,(07284h)		;9fcd	3a 84 72 	: . r 
	sub b			;9fd0	90 	. 
	jr nc,$+4		;9fd1	30 02 	0 . 
	cpl			;9fd3	2f 	/ 
	inc a			;9fd4	3c 	< 
	ld l,000h		;9fd5	2e 00 	. . 
	cp 005h		;9fd7	fe 05 	. . 
	jr nc,$+22		;9fd9	30 14 	0 . 
	ld b,(iy+001h)		;9fdb	fd 46 01 	. F . 
	ld a,(07285h)		;9fde	3a 85 72 	: . r 
	sub b			;9fe1	90 	. 
	jr nc,$+4		;9fe2	30 02 	0 . 
	cpl			;9fe4	2f 	/ 
	inc a			;9fe5	3c 	< 
	cp 005h		;9fe6	fe 05 	. . 
	jr nc,$+7		;9fe8	30 05 	0 . 
	call 0ca17h		;9fea	cd 17 ca 	. . . 
	ld l,001h		;9fed	2e 01 	. . 
	pop iy		;9fef	fd e1 	. . 
	ld a,l			;9ff1	7d 	} 
	and a			;9ff2	a7 	. 
	ret			;9ff3	c9 	. 
	push ix		;9ff4	dd e5 	. . 
	call 09f29h		;9ff6	cd 29 9f 	. ) . 
	push af			;9ff9	f5 	. 
	ld b,(iy+002h)		;9ffa	fd 46 02 	. F . 
	ld c,(iy+001h)		;9ffd	fd 4e 01 	. N . 
	call 0ac3fh		;a000	cd 3f ac 	. ? . 
	pop bc			;a003	c1 	. 
	call 0a028h		;a004	cd 28 a0 	. ( . 
	jr nz,$+5		;a007	20 03 	  . 
	call 0a1ach		;a009	cd ac a1 	. . . 
	cp 002h		;a00c	fe 02 	. . 
	jr z,$+16		;a00e	28 0e 	( . 
	ld a,(iy+004h)		;a010	fd 7e 04 	. ~ . 
	and 007h		;a013	e6 07 	. . 
	call 09d2fh		;a015	cd 2f 9d 	. / . 
	jr z,$+12		;a018	28 0a 	( . 
	cp 0ffh		;a01a	fe ff 	. . 
	jr z,$+6		;a01c	28 04 	( . 
	set 3,(iy+004h)		;a01e	fd cb 04 de 	. . . . 
	ld a,001h		;a022	3e 01 	> . 
	and a			;a024	a7 	. 
	pop ix		;a025	dd e1 	. . 
	ret			;a027	c9 	. 
	push bc			;a028	c5 	. 
	push ix		;a029	dd e5 	. . 
	push af			;a02b	f5 	. 
	ld a,(iy+002h)		;a02c	fd 7e 02 	. ~ . 
	and 00fh		;a02f	e6 0f 	. . 
	ld c,a			;a031	4f 	O 
	ld a,(iy+001h)		;a032	fd 7e 01 	. ~ . 
	rlca			;a035	07 	. 
	rlca			;a036	07 	. 
	rlca			;a037	07 	. 
	rlca			;a038	07 	. 
	and 0f0h		;a039	e6 f0 	. . 
	or c			;a03b	b1 	. 
	ld c,007h		;a03c	0e 07 	. . 
	ld hl,0a12ah		;a03e	21 2a a1 	! * . 
	cp (hl)			;a041	be 	. 
	jr z,$+11		;a042	28 09 	( . 
	inc hl			;a044	23 	# 
	inc hl			;a045	23 	# 
	inc hl			;a046	23 	# 
	dec c			;a047	0d 	. 
	jr nz,$-7		;a048	20 f7 	  . 
	dec hl			;a04a	2b 	+ 
	dec hl			;a04b	2b 	+ 
	dec hl			;a04c	2b 	+ 
	inc hl			;a04d	23 	# 
	ld e,(hl)			;a04e	5e 	^ 
	inc hl			;a04f	23 	# 
	ld d,(hl)			;a050	56 	V 
	push de			;a051	d5 	. 
	pop ix		;a052	dd e1 	. . 
	pop hl			;a054	e1 	. 
	ld a,h			;a055	7c 	| 
	ld l,0ffh		;a056	2e ff 	. . 
	call 0a13fh		;a058	cd 3f a1 	. ? . 
	jr z,$+3		;a05b	28 01 	( . 
	ld l,a			;a05d	6f 	o 
	jp (ix)		;a05e	dd e9 	. . 
	ld c,041h		;a060	0e 41 	. A 
	ld a,h			;a062	7c 	| 
	dec a			;a063	3d 	= 
	call 0a13fh		;a064	cd 3f a1 	. ? . 
	jr z,$+8		;a067	28 06 	( . 
	cp l			;a069	bd 	. 
	jr nc,$+5		;a06a	30 03 	0 . 
	ld c,082h		;a06c	0e 82 	. . 
	ld l,a			;a06e	6f 	o 
	jp 0a102h		;a06f	c3 02 a1 	. . . 
	ld c,082h		;a072	0e 82 	. . 
	ld a,h			;a074	7c 	| 
	inc a			;a075	3c 	< 
	call 0a13fh		;a076	cd 3f a1 	. ? . 
	jr z,$+8		;a079	28 06 	( . 
	cp l			;a07b	bd 	. 
	jr nc,$+5		;a07c	30 03 	0 . 
	ld l,a			;a07e	6f 	o 
	ld c,041h		;a07f	0e 41 	. A 
	jp 0a102h		;a081	c3 02 a1 	. . . 
	ld c,013h		;a084	0e 13 	. . 
	ld a,h			;a086	7c 	| 
	add a,010h		;a087	c6 10 	. . 
	call 0a13fh		;a089	cd 3f a1 	. ? . 
	jr z,$+8		;a08c	28 06 	( . 
	cp l			;a08e	bd 	. 
	jr nc,$+5		;a08f	30 03 	0 . 
	ld l,a			;a091	6f 	o 
	ld c,024h		;a092	0e 24 	. $ 
	jp 0a102h		;a094	c3 02 a1 	. . . 
	ld c,024h		;a097	0e 24 	. $ 
	ld a,h			;a099	7c 	| 
	sub 010h		;a09a	d6 10 	. . 
	call 0a13fh		;a09c	cd 3f a1 	. ? . 
	jr z,$+8		;a09f	28 06 	( . 
	cp l			;a0a1	bd 	. 
	jr nc,$+5		;a0a2	30 03 	0 . 
	ld l,a			;a0a4	6f 	o 
	ld c,013h		;a0a5	0e 13 	. . 
	jp 0a102h		;a0a7	c3 02 a1 	. . . 
	ld l,0ffh		;a0aa	2e ff 	. . 
	ld a,h			;a0ac	7c 	| 
	and 00fh		;a0ad	e6 0f 	. . 
	jr z,$+16		;a0af	28 0e 	( . 
	bit 6,b		;a0b1	cb 70 	. p 
	jr z,$+12		;a0b3	28 0a 	( . 
	ld a,h			;a0b5	7c 	| 
	inc a			;a0b6	3c 	< 
	call 0a13fh		;a0b7	cd 3f a1 	. ? . 
	jr z,$+5		;a0ba	28 03 	( . 
	ld l,a			;a0bc	6f 	o 
	ld c,041h		;a0bd	0e 41 	. A 
	ld a,h			;a0bf	7c 	| 
	dec a			;a0c0	3d 	= 
	and 00fh		;a0c1	e6 0f 	. . 
	jr z,$+19		;a0c3	28 11 	( . 
	bit 7,b		;a0c5	cb 78 	. x 
	jr z,$+15		;a0c7	28 0d 	( . 
	ld a,h			;a0c9	7c 	| 
	dec a			;a0ca	3d 	= 
	call 0a13fh		;a0cb	cd 3f a1 	. ? . 
	jr z,$+8		;a0ce	28 06 	( . 
	cp l			;a0d0	bd 	. 
	jr nc,$+5		;a0d1	30 03 	0 . 
	ld l,a			;a0d3	6f 	o 
	ld c,082h		;a0d4	0e 82 	. . 
	ld a,h			;a0d6	7c 	| 
	cp 011h		;a0d7	fe 11 	. . 
	jr c,$+19		;a0d9	38 11 	8 . 
	bit 4,b		;a0db	cb 60 	. ` 
	jr z,$+15		;a0dd	28 0d 	( . 
	sub 010h		;a0df	d6 10 	. . 
	call 0a13fh		;a0e1	cd 3f a1 	. ? . 
	jr z,$+8		;a0e4	28 06 	( . 
	cp l			;a0e6	bd 	. 
	jr nc,$+5		;a0e7	30 03 	0 . 
	ld l,a			;a0e9	6f 	o 
	ld c,013h		;a0ea	0e 13 	. . 
	ld a,h			;a0ec	7c 	| 
	cp 091h		;a0ed	fe 91 	. . 
	jr nc,$+19		;a0ef	30 11 	0 . 
	bit 5,b		;a0f1	cb 68 	. h 
	jr z,$+15		;a0f3	28 0d 	( . 
	add a,010h		;a0f5	c6 10 	. . 
	call 0a13fh		;a0f7	cd 3f a1 	. ? . 
	jr z,$+8		;a0fa	28 06 	( . 
	cp l			;a0fc	bd 	. 
	jr nc,$+5		;a0fd	30 03 	0 . 
	ld l,a			;a0ff	6f 	o 
	ld c,024h		;a100	0e 24 	. $ 
	ld d,000h		;a102	16 00 	. . 
	ld a,l			;a104	7d 	} 
	cp 0ffh		;a105	fe ff 	. . 
	jr z,$+29		;a107	28 1b 	( . 
	ld a,c			;a109	79 	y 
	and 007h		;a10a	e6 07 	. . 
	ld l,a			;a10c	6f 	o 
	ld a,(iy+004h)		;a10d	fd 7e 04 	. ~ . 
	and 0f8h		;a110	e6 f8 	. . 
	or l			;a112	b5 	. 
	ld (iy+004h),a		;a113	fd 77 04 	. w . 
	ld d,001h		;a116	16 01 	. . 
	ld a,c			;a118	79 	y 
	and 0f0h		;a119	e6 f0 	. . 
	and b			;a11b	a0 	. 
	jr nz,$+8		;a11c	20 06 	  . 
	set 0,(iy+000h)		;a11e	fd cb 00 c6 	. . . . 
	ld d,002h		;a122	16 02 	. . 
	pop ix		;a124	dd e1 	. . 
	pop bc			;a126	c1 	. 
	ld a,d			;a127	7a 	z 
	and a			;a128	a7 	. 
	ret			;a129	c9 	. 
	nop			;a12a	00 	. 
	ld h,b			;a12b	60 	` 
	and b			;a12c	a0 	. 
	ld b,b			;a12d	40 	@ 
	ld h,b			;a12e	60 	` 
	and b			;a12f	a0 	. 
	ret nz			;a130	c0 	. 
	ld (hl),d			;a131	72 	r 
	and b			;a132	a0 	. 
	add a,h			;a133	84 	. 
	add a,h			;a134	84 	. 
	and b			;a135	a0 	. 
	adc a,b			;a136	88 	. 
	sub a			;a137	97 	. 
	and b			;a138	a0 	. 
	adc a,h			;a139	8c 	. 
	sub a			;a13a	97 	. 
	and b			;a13b	a0 	. 
	add a,b			;a13c	80 	. 
	xor d			;a13d	aa 	. 
	and b			;a13e	a0 	. 
	push bc			;a13f	c5 	. 
	push de			;a140	d5 	. 
	push hl			;a141	e5 	. 
	push ix		;a142	dd e5 	. . 
	ld d,a			;a144	57 	W 
	ld a,(07139h)		;a145	3a 39 71 	: 9 q 
	and a			;a148	a7 	. 
	jr z,$+16		;a149	28 0e 	( . 
	ld c,a			;a14b	4f 	O 
	ld b,000h		;a14c	06 00 	. . 
	dec bc			;a14e	0b 	. 
	ld hl,0713ah		;a14f	21 3a 71 	! : q 
	add hl,bc			;a152	09 	. 
	inc bc			;a153	03 	. 
	ld a,d			;a154	7a 	z 
	cpdr		;a155	ed b9 	. . 
	jr z,$+43		;a157	28 29 	( ) 
	ld hl,0713ah		;a159	21 3a 71 	! : q 
	ld bc,0004fh		;a15c	01 4f 00 	. O . 
	add hl,bc			;a15f	09 	. 
	push hl			;a160	e5 	. 
	pop ix		;a161	dd e1 	. . 
	ld hl,0713ah		;a163	21 3a 71 	! : q 
	ld a,(07139h)		;a166	3a 39 71 	: 9 q 
	ld c,a			;a169	4f 	O 
	ld b,000h		;a16a	06 00 	. . 
	add hl,bc			;a16c	09 	. 
	ld b,h			;a16d	44 	D 
	ld c,l			;a16e	4d 	M 
	push ix		;a16f	dd e5 	. . 
	pop hl			;a171	e1 	. 
	xor a			;a172	af 	. 
	sbc hl,bc		;a173	ed 42 	. B 
	jr z,$+47		;a175	28 2d 	( - 
	inc hl			;a177	23 	# 
	ld b,h			;a178	44 	D 
	ld c,l			;a179	4d 	M 
	push ix		;a17a	dd e5 	. . 
	pop hl			;a17c	e1 	. 
	ld a,d			;a17d	7a 	z 
	cpdr		;a17e	ed b9 	. . 
	jr nz,$+36		;a180	20 22 	  " 
	inc hl			;a182	23 	# 
	push hl			;a183	e5 	. 
	ld hl,0713ah		;a184	21 3a 71 	! : q 
	ld a,(07139h)		;a187	3a 39 71 	: 9 q 
	ld c,a			;a18a	4f 	O 
	ld b,000h		;a18b	06 00 	. . 
	and a			;a18d	a7 	. 
	jr nz,$+5		;a18e	20 03 	  . 
	ld bc,00050h		;a190	01 50 00 	. P . 
	dec bc			;a193	0b 	. 
	add hl,bc			;a194	09 	. 
	pop bc			;a195	c1 	. 
	xor a			;a196	af 	. 
	sbc hl,bc		;a197	ed 42 	. B 
	jr nc,$+7		;a199	30 05 	0 . 
	ld bc,00050h		;a19b	01 50 00 	. P . 
	xor a			;a19e	af 	. 
	add hl,bc			;a19f	09 	. 
	inc l			;a1a0	2c 	, 
	ld a,l			;a1a1	7d 	} 
	jr $+3		;a1a2	18 01 	. . 
	xor a			;a1a4	af 	. 
	pop ix		;a1a5	dd e1 	. . 
	pop hl			;a1a7	e1 	. 
	pop de			;a1a8	d1 	. 
	pop bc			;a1a9	c1 	. 
	and a			;a1aa	a7 	. 
	ret			;a1ab	c9 	. 
	ld l,000h		;a1ac	2e 00 	. . 
	ld h,(iy+001h)		;a1ae	fd 66 01 	. f . 
	ld a,(07285h)		;a1b1	3a 85 72 	: . r 
	cp h			;a1b4	bc 	. 
	jr z,$+10		;a1b5	28 08 	( . 
	jr c,$+6		;a1b7	38 04 	8 . 
	set 6,l		;a1b9	cb f5 	. . 
	jr $+4		;a1bb	18 02 	. . 
	set 7,l		;a1bd	cb fd 	. . 
	ld h,(iy+002h)		;a1bf	fd 66 02 	. f . 
	ld a,(07284h)		;a1c2	3a 84 72 	: . r 
	cp h			;a1c5	bc 	. 
	jr z,$+10		;a1c6	28 08 	( . 
	jr c,$+6		;a1c8	38 04 	8 . 
	set 5,l		;a1ca	cb ed 	. . 
	jr $+4		;a1cc	18 02 	. . 
	set 4,l		;a1ce	cb e5 	. . 
	ld a,l			;a1d0	7d 	} 
	and b			;a1d1	a0 	. 
	jr nz,$+6		;a1d2	20 04 	  . 
	ld a,002h		;a1d4	3e 02 	> . 
	jr $+7		;a1d6	18 05 	. . 
	call 09e7ah		;a1d8	cd 7a 9e 	. z . 
	ld a,001h		;a1db	3e 01 	> . 
	and a			;a1dd	a7 	. 
	ret			;a1de	c9 	. 
	push ix		;a1df	dd e5 	. . 
	ld b,000h		;a1e1	06 00 	. . 
	bit 5,(iy+004h)		;a1e3	fd cb 04 6e 	. . . n 
	jr nz,$+39		;a1e7	20 25 	  % 
	bit 1,(iy+000h)		;a1e9	fd cb 00 4e 	. . . N 
	jr z,$+103		;a1ed	28 65 	( e 
	ld a,(iy+004h)		;a1ef	fd 7e 04 	. ~ . 
	and 007h		;a1f2	e6 07 	. . 
	dec a			;a1f4	3d 	= 
	cp 004h		;a1f5	fe 04 	. . 
	jr nc,$+93		;a1f7	30 5b 	0 [ 
	ld hl,09f25h		;a1f9	21 25 9f 	! % . 
	ld c,a			;a1fc	4f 	O 
	ld b,000h		;a1fd	06 00 	. . 
	add hl,bc			;a1ff	09 	. 
	ld c,(hl)			;a200	4e 	N 
	push bc			;a201	c5 	. 
	call 09f29h		;a202	cd 29 9f 	. ) . 
	pop bc			;a205	c1 	. 
	and a			;a206	a7 	. 
	jr z,$+77		;a207	28 4b 	( K 
	and c			;a209	a1 	. 
	jr nz,$+72		;a20a	20 46 	  F 
	jr $+18		;a20c	18 10 	. . 
	res 1,(iy+000h)		;a20e	fd cb 00 8e 	. . . . 
	call 09ce0h		;a212	cd e0 9c 	. . . 
	ld c,a			;a215	4f 	O 
	call 01ffdh		;a216	cd fd 1f 	. . . 
	and 00fh		;a219	e6 0f 	. . 
	cp c			;a21b	b9 	. 
	jr nc,$+56		;a21c	30 36 	0 6 
	ld a,(iy+000h)		;a21e	fd 7e 00 	. ~ . 
	and 0f8h		;a221	e6 f8 	. . 
	ld (iy+000h),a		;a223	fd 77 00 	. w . 
	ld b,(iy+002h)		;a226	fd 46 02 	. F . 
	ld c,(iy+001h)		;a229	fd 4e 01 	. N . 
	call 0ac3fh		;a22c	cd 3f ac 	. ? . 
	ld e,a			;a22f	5f 	_ 
	call 0a259h		;a230	cd 59 a2 	. Y . 
	jr nz,$+14		;a233	20 0c 	  . 
	call 0a382h		;a235	cd 82 a3 	. . . 
	jr z,$+9		;a238	28 07 	( . 
	call 0a402h		;a23a	cd 02 a4 	. . . 
	ld b,000h		;a23d	06 00 	. . 
	jr nz,$+21		;a23f	20 13 	  . 
	push hl			;a241	e5 	. 
	call 09f29h		;a242	cd 29 9f 	. ) . 
	pop hl			;a245	e1 	. 
	ld b,000h		;a246	06 00 	. . 
	and l			;a248	a5 	. 
	jr z,$+11		;a249	28 09 	( . 
	call 09e7ah		;a24b	cd 7a 9e 	. z . 
	set 1,(iy+000h)		;a24e	fd cb 00 ce 	. . . . 
	ld b,001h		;a252	06 01 	. . 
	ld a,b			;a254	78 	x 
	pop ix		;a255	dd e1 	. . 
	and a			;a257	a7 	. 
	ret			;a258	c9 	. 
	push ix		;a259	dd e5 	. . 
	push de			;a25b	d5 	. 
	push bc			;a25c	c5 	. 
	ld a,(072d9h)		;a25d	3a d9 72 	: . r 
	ld b,a			;a260	47 	G 
	xor a			;a261	af 	. 
	bit 6,b		;a262	cb 70 	. p 
	jr z,$+85		;a264	28 53 	( S 
	push de			;a266	d5 	. 
	ld a,e			;a267	7b 	{ 
	call 0abb7h		;a268	cd b7 ab 	. . . 
	push bc			;a26b	c5 	. 
	ld a,(072dah)		;a26c	3a da 72 	: . r 
	ld b,a			;a26f	47 	G 
	ld a,(072dbh)		;a270	3a db 72 	: . r 
	ld c,a			;a273	4f 	O 
	call 0ac3fh		;a274	cd 3f ac 	. ? . 
	push af			;a277	f5 	. 
	push ix		;a278	dd e5 	. . 
	call 0abb7h		;a27a	cd b7 ab 	. . . 
	pop ix		;a27d	dd e1 	. . 
	pop af			;a27f	f1 	. 
	pop hl			;a280	e1 	. 
	pop de			;a281	d1 	. 
	ld d,a			;a282	57 	W 
	sub e			;a283	93 	. 
	jr z,$+53		;a284	28 33 	( 3 
	ld a,(072d9h)		;a286	3a d9 72 	: . r 
	and 003h		;a289	e6 03 	. . 
	jr nz,$+12		;a28b	20 0a 	  . 
	call 0a2c0h		;a28d	cd c0 a2 	. . . 
	jr nz,$+41		;a290	20 27 	  ' 
	call 0a34ch		;a292	cd 4c a3 	. L . 
	jr $+36		;a295	18 22 	. " 
	dec a			;a297	3d 	= 
	jr nz,$+12		;a298	20 0a 	  . 
	call 0a2e8h		;a29a	cd e8 a2 	. . . 
	jr nz,$+28		;a29d	20 1a 	  . 
	call 0a34ch		;a29f	cd 4c a3 	. L . 
	jr $+23		;a2a2	18 15 	. . 
	dec a			;a2a4	3d 	= 
	jr nz,$+12		;a2a5	20 0a 	  . 
	call 0a2c0h		;a2a7	cd c0 a2 	. . . 
	jr nz,$+15		;a2aa	20 0d 	  . 
	call 0a316h		;a2ac	cd 16 a3 	. . . 
	jr $+10		;a2af	18 08 	. . 
	call 0a2e8h		;a2b1	cd e8 a2 	. . . 
	jr nz,$+5		;a2b4	20 03 	  . 
	call 0a316h		;a2b6	cd 16 a3 	. . . 
	ld l,a			;a2b9	6f 	o 
	pop bc			;a2ba	c1 	. 
	pop de			;a2bb	d1 	. 
	pop ix		;a2bc	dd e1 	. . 
	and a			;a2be	a7 	. 
	ret			;a2bf	c9 	. 
	push de			;a2c0	d5 	. 
	push hl			;a2c1	e5 	. 
	ld a,b			;a2c2	78 	x 
	cp h			;a2c3	bc 	. 
	jr nz,$+31		;a2c4	20 1d 	  . 
	ld a,l			;a2c6	7d 	} 
	sub c			;a2c7	91 	. 
	jr c,$+27		;a2c8	38 19 	8 . 
	cp 021h		;a2ca	fe 21 	. ! 
	jr nc,$+23		;a2cc	30 15 	0 . 
	inc d			;a2ce	14 	. 
	bit 6,(ix+000h)		;a2cf	dd cb 00 76 	. . . v 
	jr z,$+16		;a2d3	28 0e 	( . 
	ld a,e			;a2d5	7b 	{ 
	cp d			;a2d6	ba 	. 
	jr z,$+8		;a2d7	28 06 	( . 
	bit 6,(ix+001h)		;a2d9	dd cb 01 76 	. . . v 
	jr z,$+6		;a2dd	28 04 	( . 
	ld a,070h		;a2df	3e 70 	> p 
	jr $+3		;a2e1	18 01 	. . 
	xor a			;a2e3	af 	. 
	pop hl			;a2e4	e1 	. 
	pop de			;a2e5	d1 	. 
	and a			;a2e6	a7 	. 
	ret			;a2e7	c9 	. 
	push de			;a2e8	d5 	. 
	push hl			;a2e9	e5 	. 
	push ix		;a2ea	dd e5 	. . 
	ld a,b			;a2ec	78 	x 
	cp h			;a2ed	bc 	. 
	jr nz,$+33		;a2ee	20 1f 	  . 
	ld a,c			;a2f0	79 	y 
	sub l			;a2f1	95 	. 
	jr c,$+29		;a2f2	38 1b 	8 . 
	cp 021h		;a2f4	fe 21 	. ! 
	jr nc,$+25		;a2f6	30 17 	0 . 
	dec d			;a2f8	15 	. 
	bit 7,(ix+000h)		;a2f9	dd cb 00 7e 	. . . ~ 
	jr z,$+18		;a2fd	28 10 	( . 
	ld a,e			;a2ff	7b 	{ 
	cp d			;a300	ba 	. 
	jr z,$+10		;a301	28 08 	( . 
	dec ix		;a303	dd 2b 	. + 
	bit 7,(ix+000h)		;a305	dd cb 00 7e 	. . . ~ 
	jr z,$+6		;a309	28 04 	( . 
	ld a,0b0h		;a30b	3e b0 	> . 
	jr $+3		;a30d	18 01 	. . 
	xor a			;a30f	af 	. 
	pop ix		;a310	dd e1 	. . 
	pop hl			;a312	e1 	. 
	pop de			;a313	d1 	. 
	and a			;a314	a7 	. 
	ret			;a315	c9 	. 
	push de			;a316	d5 	. 
	push hl			;a317	e5 	. 
	push ix		;a318	dd e5 	. . 
	ld a,c			;a31a	79 	y 
	cp l			;a31b	bd 	. 
	jr nz,$+41		;a31c	20 27 	  ' 
	ld a,b			;a31e	78 	x 
	sub h			;a31f	94 	. 
	jr c,$+37		;a320	38 23 	8 # 
	cp 021h		;a322	fe 21 	. ! 
	jr nc,$+33		;a324	30 1f 	0 . 
	ld a,d			;a326	7a 	z 
	sub 010h		;a327	d6 10 	. . 
	ld d,a			;a329	57 	W 
	bit 4,(ix+000h)		;a32a	dd cb 00 66 	. . . f 
	jr z,$+23		;a32e	28 15 	( . 
	ld a,e			;a330	7b 	{ 
	cp d			;a331	ba 	. 
	jr z,$+15		;a332	28 0d 	( . 
	push bc			;a334	c5 	. 
	ld bc,0fff0h		;a335	01 f0 ff 	. . . 
	add ix,bc		;a338	dd 09 	. . 
	pop bc			;a33a	c1 	. 
	bit 4,(ix+000h)		;a33b	dd cb 00 66 	. . . f 
	jr z,$+6		;a33f	28 04 	( . 
	ld a,0d0h		;a341	3e d0 	> . 
	jr $+3		;a343	18 01 	. . 
	xor a			;a345	af 	. 
	pop ix		;a346	dd e1 	. . 
	pop hl			;a348	e1 	. 
	pop de			;a349	d1 	. 
	and a			;a34a	a7 	. 
	ret			;a34b	c9 	. 
	push de			;a34c	d5 	. 
	push hl			;a34d	e5 	. 
	push ix		;a34e	dd e5 	. . 
	ld a,c			;a350	79 	y 
	cp l			;a351	bd 	. 
	jr nz,$+41		;a352	20 27 	  ' 
	ld a,h			;a354	7c 	| 
	sub b			;a355	90 	. 
	jr c,$+37		;a356	38 23 	8 # 
	cp 021h		;a358	fe 21 	. ! 
	jr nc,$+33		;a35a	30 1f 	0 . 
	ld a,d			;a35c	7a 	z 
	add a,010h		;a35d	c6 10 	. . 
	ld d,a			;a35f	57 	W 
	bit 5,(ix+000h)		;a360	dd cb 00 6e 	. . . n 
	jr z,$+23		;a364	28 15 	( . 
	ld a,e			;a366	7b 	{ 
	cp d			;a367	ba 	. 
	jr z,$+15		;a368	28 0d 	( . 
	push bc			;a36a	c5 	. 
	ld bc,00010h		;a36b	01 10 00 	. . . 
	add ix,bc		;a36e	dd 09 	. . 
	pop bc			;a370	c1 	. 
	bit 5,(ix+000h)		;a371	dd cb 00 6e 	. . . n 
	jr z,$+6		;a375	28 04 	( . 
	ld a,0e0h		;a377	3e e0 	> . 
	jr $+3		;a379	18 01 	. . 
	xor a			;a37b	af 	. 
	pop ix		;a37c	dd e1 	. . 
	pop hl			;a37e	e1 	. 
	pop de			;a37f	d1 	. 
	and a			;a380	a7 	. 
	ret			;a381	c9 	. 
	push bc			;a382	c5 	. 
	push de			;a383	d5 	. 
	push ix		;a384	dd e5 	. . 
	push iy		;a386	fd e5 	. . 
	ld a,e			;a388	7b 	{ 
	push de			;a389	d5 	. 
	call 0abb7h		;a38a	cd b7 ab 	. . . 
	pop de			;a38d	d1 	. 
	ld l,005h		;a38e	2e 05 	. . 
	ld iy,0722ch		;a390	fd 21 2c 72 	. ! , r 
	bit 7,(iy+000h)		;a394	fd cb 00 7e 	. . . ~ 
	jr z,$+86		;a398	28 54 	( T 
	bit 5,(iy+000h)		;a39a	fd cb 00 6e 	. . . n 
	jr z,$+80		;a39e	28 4e 	( N 
	ld a,c			;a3a0	79 	y 
	cp (iy+002h)		;a3a1	fd be 02 	. . . 
	jr nz,$+74		;a3a4	20 48 	  H 
	ld a,b			;a3a6	78 	x 
	cp (iy+001h)		;a3a7	fd be 01 	. . . 
	jr c,$+68		;a3aa	38 42 	8 B 
	push bc			;a3ac	c5 	. 
	push de			;a3ad	d5 	. 
	push hl			;a3ae	e5 	. 
	push ix		;a3af	dd e5 	. . 
	ld b,(iy+001h)		;a3b1	fd 46 01 	. F . 
	ld c,(iy+002h)		;a3b4	fd 4e 02 	. N . 
	call 0ac3fh		;a3b7	cd 3f ac 	. ? . 
	pop ix		;a3ba	dd e1 	. . 
	pop hl			;a3bc	e1 	. 
	pop de			;a3bd	d1 	. 
	pop bc			;a3be	c1 	. 
	ld h,a			;a3bf	67 	g 
	ld d,e			;a3c0	53 	S 
	push bc			;a3c1	c5 	. 
	ld bc,0fff0h		;a3c2	01 f0 ff 	. . . 
	add ix,bc		;a3c5	dd 09 	. . 
	pop bc			;a3c7	c1 	. 
	ld a,d			;a3c8	7a 	z 
	sub 010h		;a3c9	d6 10 	. . 
	ld d,a			;a3cb	57 	W 
	ld a,(ix+000h)		;a3cc	dd 7e 00 	. ~ . 
	and 00fh		;a3cf	e6 0f 	. . 
	cp 00fh		;a3d1	fe 0f 	. . 
	jr nz,$+27		;a3d3	20 19 	  . 
	ld a,h			;a3d5	7c 	| 
	cp d			;a3d6	ba 	. 
	jr c,$-22		;a3d7	38 e8 	8 . 
	ld l,0e0h		;a3d9	2e e0 	. . 
	pop iy		;a3db	fd e1 	. . 
	ld a,(iy+001h)		;a3dd	fd 7e 01 	. ~ . 
	cp c			;a3e0	b9 	. 
	jr z,$+10		;a3e1	28 08 	( . 
	res 7,l		;a3e3	cb bd 	. . 
	jr nc,$+6		;a3e5	30 04 	0 . 
	set 7,l		;a3e7	cb fd 	. . 
	res 6,l		;a3e9	cb b5 	. . 
	xor a			;a3eb	af 	. 
	jr $+16		;a3ec	18 0e 	. . 
	push bc			;a3ee	c5 	. 
	ld bc,00005h		;a3ef	01 05 00 	. . . 
	add iy,bc		;a3f2	fd 09 	. . 
	pop bc			;a3f4	c1 	. 
	dec l			;a3f5	2d 	- 
	jr nz,$-98		;a3f6	20 9c 	  . 
	ld a,001h		;a3f8	3e 01 	> . 
	pop iy		;a3fa	fd e1 	. . 
	pop ix		;a3fc	dd e1 	. . 
	pop de			;a3fe	d1 	. 
	pop bc			;a3ff	c1 	. 
	and a			;a400	a7 	. 
	ret			;a401	c9 	. 
	push bc			;a402	c5 	. 
	push de			;a403	d5 	. 
	push ix		;a404	dd e5 	. . 
	ld b,(iy+002h)		;a406	fd 46 02 	. F . 
	ld c,(iy+001h)		;a409	fd 4e 01 	. N . 
	ld l,005h		;a40c	2e 05 	. . 
	ld ix,0722ch		;a40e	dd 21 2c 72 	. ! , r 
	bit 7,(ix+000h)		;a412	dd cb 00 7e 	. . . ~ 
	jr z,$+55		;a416	28 35 	( 5 
	bit 6,(ix+000h)		;a418	dd cb 00 76 	. . . v 
	jr z,$+49		;a41c	28 2f 	( / 
	ld d,(ix+001h)		;a41e	dd 56 01 	. V . 
	ld e,(ix+002h)		;a421	dd 5e 02 	. ^ . 
	ld a,b			;a424	78 	x 
	cp d			;a425	ba 	. 
	jr c,$+39		;a426	38 25 	8 % 
	sub d			;a428	92 	. 
	cp 021h		;a429	fe 21 	. ! 
	jr nc,$+34		;a42b	30 20 	0   
	ld a,c			;a42d	79 	y 
	sub e			;a42e	93 	. 
	jr nc,$+4		;a42f	30 02 	0 . 
	cpl			;a431	2f 	/ 
	inc a			;a432	3c 	< 
	cp 011h		;a433	fe 11 	. . 
	jr nc,$+24		;a435	30 16 	0 . 
	ld h,000h		;a437	26 00 	& . 
	ld a,(iy+001h)		;a439	fd 7e 01 	. ~ . 
	ld l,0e0h		;a43c	2e e0 	. . 
	cp (ix+002h)		;a43e	dd be 02 	. . . 
	jr z,$+24		;a441	28 16 	( . 
	res 7,l		;a443	cb bd 	. . 
	jr nc,$+20		;a445	30 12 	0 . 
	set 7,l		;a447	cb fd 	. . 
	res 6,l		;a449	cb b5 	. . 
	jr $+14		;a44b	18 0c 	. . 
	push bc			;a44d	c5 	. 
	ld bc,00005h		;a44e	01 05 00 	. . . 
	add ix,bc		;a451	dd 09 	. . 
	pop bc			;a453	c1 	. 
	dec l			;a454	2d 	- 
	jr nz,$-67		;a455	20 bb 	  . 
	ld h,001h		;a457	26 01 	& . 
	pop ix		;a459	dd e1 	. . 
	pop de			;a45b	d1 	. 
	pop bc			;a45c	c1 	. 
	ld a,h			;a45d	7c 	| 
	and a			;a45e	a7 	. 
	ret			;a45f	c9 	. 
	call 0a497h		;a460	cd 97 a4 	. . . 
	jr z,$+51		;a463	28 31 	( 1 
	ld l,a			;a465	6f 	o 
	push hl			;a466	e5 	. 
	call 09e7ah		;a467	cd 7a 9e 	. z . 
	ld a,(iy+004h)		;a46a	fd 7e 04 	. ~ . 
	and 007h		;a46d	e6 07 	. . 
	call 09d2fh		;a46f	cd 2f 9d 	. / . 
	pop hl			;a472	e1 	. 
	jr z,$+35		;a473	28 21 	( ! 
	ld a,(iy+004h)		;a475	fd 7e 04 	. ~ . 
	and 007h		;a478	e6 07 	. . 
	ld c,0c0h		;a47a	0e c0 	. . 
	cp 003h		;a47c	fe 03 	. . 
	jr nc,$+4		;a47e	30 02 	0 . 
	ld c,030h		;a480	0e 30 	. 0 
	ld a,l			;a482	7d 	} 
	and c			;a483	a1 	. 
	jr nz,$-31		;a484	20 df 	  . 
	ld a,(iy+004h)		;a486	fd 7e 04 	. ~ . 
	bit 0,a		;a489	cb 47 	. G 
	jr z,$+5		;a48b	28 03 	( . 
	inc a			;a48d	3c 	< 
	jr $+3		;a48e	18 01 	. . 
	dec a			;a490	3d 	= 
	ld (iy+004h),a		;a491	fd 77 04 	. w . 
	jr $+2		;a494	18 00 	. . 
	ret			;a496	c9 	. 
	ld a,(iy+002h)		;a497	fd 7e 02 	. ~ . 
	ld b,a			;a49a	47 	G 
	and 00fh		;a49b	e6 0f 	. . 
	jr nz,$+117		;a49d	20 73 	  s 
	ld a,(iy+001h)		;a49f	fd 7e 01 	. ~ . 
	ld c,a			;a4a2	4f 	O 
	and 00fh		;a4a3	e6 0f 	. . 
	cp 008h		;a4a5	fe 08 	. . 
	jr nz,$+107		;a4a7	20 69 	  i 
	ld h,000h		;a4a9	26 00 	& . 
	ld a,(07284h)		;a4ab	3a 84 72 	: . r 
	cp b			;a4ae	b8 	. 
	jr z,$+10		;a4af	28 08 	( . 
	jr nc,$+6		;a4b1	30 04 	0 . 
	set 4,h		;a4b3	cb e4 	. . 
	jr $+4		;a4b5	18 02 	. . 
	set 5,h		;a4b7	cb ec 	. . 
	ld a,(07285h)		;a4b9	3a 85 72 	: . r 
	cp c			;a4bc	b9 	. 
	jr z,$+99		;a4bd	28 61 	( a 
	ld a,c			;a4bf	79 	y 
	jr c,$+8		;a4c0	38 06 	8 . 
	set 6,h		;a4c2	cb f4 	. . 
	add a,010h		;a4c4	c6 10 	. . 
	jr $+6		;a4c6	18 04 	. . 
	set 7,h		;a4c8	cb fc 	. . 
	sub 010h		;a4ca	d6 10 	. . 
	ld c,a			;a4cc	4f 	O 
	ld ix,0722ch		;a4cd	dd 21 2c 72 	. ! , r 
	ld l,005h		;a4d1	2e 05 	. . 
	bit 7,(ix+000h)		;a4d3	dd cb 00 7e 	. . . ~ 
	jr z,$+28		;a4d7	28 1a 	( . 
	ld a,(ix+001h)		;a4d9	dd 7e 01 	. ~ . 
	sub 009h		;a4dc	d6 09 	. . 
	cp b			;a4de	b8 	. 
	jr nc,$+20		;a4df	30 12 	0 . 
	add a,012h		;a4e1	c6 12 	. . 
	cp b			;a4e3	b8 	. 
	jr c,$+15		;a4e4	38 0d 	8 . 
	ld a,(ix+002h)		;a4e6	dd 7e 02 	. ~ . 
	sub 00fh		;a4e9	d6 0f 	. . 
	cp c			;a4eb	b9 	. 
	jr nc,$+7		;a4ec	30 05 	0 . 
	add a,01fh		;a4ee	c6 1f 	. . 
	cp c			;a4f0	b9 	. 
	jr nc,$+12		;a4f1	30 0a 	0 . 
	ld de,00005h		;a4f3	11 05 00 	. . . 
	add ix,de		;a4f6	dd 19 	. . 
	dec l			;a4f8	2d 	- 
	jr nz,$-38		;a4f9	20 d8 	  . 
	jr $+37		;a4fb	18 23 	. # 
	ld a,h			;a4fd	7c 	| 
	and 030h		;a4fe	e6 30 	. 0 
	ld h,a			;a500	67 	g 
	jr nz,$+31		;a501	20 1d 	  . 
	set 4,h		;a503	cb e4 	. . 
	ld a,(iy+002h)		;a505	fd 7e 02 	. ~ . 
	cp 030h		;a508	fe 30 	. 0 
	jr nc,$+22		;a50a	30 14 	0 . 
	res 4,h		;a50c	cb a4 	. . 
	set 5,h		;a50e	cb ec 	. . 
	jr $+16		;a510	18 0e 	. . 
	ld a,(iy+004h)		;a512	fd 7e 04 	. ~ . 
	and 007h		;a515	e6 07 	. . 
	dec a			;a517	3d 	= 
	ld e,a			;a518	5f 	_ 
	ld d,000h		;a519	16 00 	. . 
	ld hl,0a523h		;a51b	21 23 a5 	! # . 
	add hl,de			;a51e	19 	. 
	ld h,(hl)			;a51f	66 	f 
	ld a,h			;a520	7c 	| 
	and a			;a521	a7 	. 
	ret			;a522	c9 	. 
	ld b,b			;a523	40 	@ 
	add a,b			;a524	80 	. 
	djnz $+34		;a525	10 20 	.   
	push bc			;a527	c5 	. 
	ld a,(0726eh)		;a528	3a 6e 72 	: n r 
	ld b,a			;a52b	47 	G 
	ld a,(07278h)		;a52c	3a 78 72 	: x r 
	bit 0,b		;a52f	cb 40 	. @ 
	jr z,$+9		;a531	28 07 	( . 
	bit 1,b		;a533	cb 48 	. H 
	jr z,$+5		;a535	28 03 	( . 
	ld a,(07279h)		;a537	3a 79 72 	: y r 
	cp 001h		;a53a	fe 01 	. . 
	pop bc			;a53c	c1 	. 
	ret			;a53d	c9 	. 
	ld a,(072bah)		;a53e	3a ba 72 	: . r 
	bit 7,a		;a541	cb 7f 	.  
	jr nz,$+14		;a543	20 0c 	  . 
	set 7,a		;a545	cb ff 	. . 
	ld (072bah),a		;a547	32 ba 72 	2 . r 
	ld a,040h		;a54a	3e 40 	> @ 
	ld (072bdh),a		;a54c	32 bd 72 	2 . r 
	jr $+87		;a54f	18 55 	. U 
	ld a,(072bdh)		;a551	3a bd 72 	: . r 
	bit 7,a		;a554	cb 7f 	.  
	ld a,000h		;a556	3e 00 	> . 
	jr nz,$+99		;a558	20 61 	  a 
	ld a,(072c0h)		;a55a	3a c0 72 	: . r 
	call 01fd0h		;a55d	cd d0 1f 	. . . 
	and a			;a560	a7 	. 
	jr z,$+90		;a561	28 58 	( X 
	ld a,(072bah)		;a563	3a ba 72 	: . r 
	bit 6,a		;a566	cb 77 	. w 
	jr z,$+7		;a568	28 05 	( . 
	call 0a6bbh		;a56a	cd bb a6 	. . . 
	jr $+61		;a56d	18 3b 	. ; 
	ld a,(07272h)		;a56f	3a 72 72 	: r r 
	bit 5,a		;a572	cb 6f 	. o 
	jr nz,$+7		;a574	20 05 	  . 
	call 0a61fh		;a576	cd 1f a6 	. . . 
	jr z,$+24		;a579	28 16 	( . 
	call 0a5f9h		;a57b	cd f9 a5 	. . . 
	jr nz,$+19		;a57e	20 11 	  . 
	call 0a662h		;a580	cd 62 a6 	. b . 
	ld hl,07272h		;a583	21 72 72 	! r r 
	bit 5,(hl)		;a586	cb 6e 	. n 
	jr z,$+33		;a588	28 1f 	( . 
	res 5,(hl)		;a58a	cb ae 	. . 
	call 0b8a3h		;a58c	cd a3 b8 	. . . 
	jr $+26		;a58f	18 18 	. . 
	jp 0d309h		;a591	c3 09 d3 	. . . 
	nop			;a594	00 	. 
	nop			;a595	00 	. 
	ld a,(07272h)		;a596	3a 72 72 	: r r 
	bit 4,a		;a599	cb 67 	. g 
	jr nz,$+14		;a59b	20 0c 	  . 
	ld a,(072c2h)		;a59d	3a c2 72 	: . r 
	dec a			;a5a0	3d 	= 
	ld (072c2h),a		;a5a1	32 c2 72 	2 . r 
	jr nz,$+5		;a5a4	20 03 	  . 
	call 0a5bdh		;a5a6	cd bd a5 	. . . 
	xor a			;a5a9	af 	. 
	push af			;a5aa	f5 	. 
	ld hl,0000ah		;a5ab	21 0a 00 	! . . 
	xor a			;a5ae	af 	. 
	call 01fcdh		;a5af	cd cd 1f 	. . . 
	ld (072c0h),a		;a5b2	32 c0 72 	2 . r 
	pop af			;a5b5	f1 	. 
	push af			;a5b6	f5 	. 
	call 0a788h		;a5b7	cd 88 a7 	. . . 
	pop af			;a5ba	f1 	. 
	and a			;a5bb	a7 	. 
	ret			;a5bc	c9 	. 
	ld a,(072bah)		;a5bd	3a ba 72 	: . r 
	inc a			;a5c0	3c 	< 
	and 0f7h		;a5c1	e6 f7 	. . 
	ld (072bah),a		;a5c3	32 ba 72 	2 . r 
	ld hl,0a5f1h		;a5c6	21 f1 a5 	! . . 
	ld a,(072bah)		;a5c9	3a ba 72 	: . r 
	and 007h		;a5cc	e6 07 	. . 
	ld c,a			;a5ce	4f 	O 
	ld b,000h		;a5cf	06 00 	. . 
	add hl,bc			;a5d1	09 	. 
	ld a,(hl)			;a5d2	7e 	~ 
	ld (072beh),a		;a5d3	32 be 72 	2 . r 
	ld a,00ch		;a5d6	3e 0c 	> . 
	ld (072bfh),a		;a5d8	32 bf 72 	2 . r 
	ld hl,0a616h		;a5db	21 16 a6 	! . . 
	add hl,bc			;a5de	09 	. 
	ld a,(hl)			;a5df	7e 	~ 
	ld (072bch),a		;a5e0	32 bc 72 	2 . r 
	ld hl,0a617h		;a5e3	21 17 a6 	! . . 
	add hl,bc			;a5e6	09 	. 
	ld a,(hl)			;a5e7	7e 	~ 
	ld (072bbh),a		;a5e8	32 bb 72 	2 . r 
	ld a,018h		;a5eb	3e 18 	> . 
	ld (072c2h),a		;a5ed	32 c2 72 	2 . r 
	ret			;a5f0	c9 	. 
	ld e,e			;a5f1	5b 	[ 
	ld l,e			;a5f2	6b 	k 
	ld a,e			;a5f3	7b 	{ 
	adc a,e			;a5f4	8b 	. 
	sbc a,e			;a5f5	9b 	. 
	adc a,e			;a5f6	8b 	. 
	ld a,e			;a5f7	7b 	{ 
	ld l,e			;a5f8	6b 	k 
	ld a,(072bah)		;a5f9	3a ba 72 	: . r 
	and 007h		;a5fc	e6 07 	. . 
	ld c,a			;a5fe	4f 	O 
	ld b,000h		;a5ff	06 00 	. . 
	ld hl,0a617h		;a601	21 17 a6 	! . . 
	add hl,bc			;a604	09 	. 
	ld b,(hl)			;a605	46 	F 
	ld hl,072b8h		;a606	21 b8 72 	! . r 
	ld a,(0726eh)		;a609	3a 6e 72 	: n r 
	and 003h		;a60c	e6 03 	. . 
	cp 003h		;a60e	fe 03 	. . 
	jr nz,$+3		;a610	20 01 	  . 
	inc hl			;a612	23 	# 
	ld a,(hl)			;a613	7e 	~ 
	and b			;a614	a0 	. 
	ret			;a615	c9 	. 
	ld (bc),a			;a616	02 	. 
	ld bc,00402h		;a617	01 02 04 	. . . 
	ex af,af'			;a61a	08 	. 
	djnz $+10		;a61b	10 08 	. . 
	inc b			;a61d	04 	. 
	ld (bc),a			;a61e	02 	. 
	ld hl,0727ah		;a61f	21 7a 72 	! z r 
	ld bc,(0727dh)		;a622	ed 4b 7d 72 	. K } r 
	ld hl,0727ah		;a626	21 7a 72 	! z r 
	ld a,(0726eh)		;a629	3a 6e 72 	: n r 
	and 003h		;a62c	e6 03 	. . 
	cp 003h		;a62e	fe 03 	. . 
	jr nz,$+7		;a630	20 05 	  . 
	ld bc,(0727fh)		;a632	ed 4b 7f 72 	. K  r 
	inc hl			;a636	23 	# 
	ld d,(hl)			;a637	56 	V 
	ld e,000h		;a638	1e 00 	. . 
	ld a,c			;a63a	79 	y 
	sub 0e8h		;a63b	d6 e8 	. . 
	ld c,a			;a63d	4f 	O 
	ld a,b			;a63e	78 	x 
	sbc a,003h		;a63f	de 03 	. . 
	ld b,a			;a641	47 	G 
	jr c,$+5		;a642	38 03 	8 . 
	inc e			;a644	1c 	. 
	jr $-11		;a645	18 f3 	. . 
	ld a,e			;a647	7b 	{ 
	ld e,000h		;a648	1e 00 	. . 
	cp d			;a64a	ba 	. 
	jr z,$+20		;a64b	28 12 	( . 
	ld (hl),a			;a64d	77 	w 
	ld a,(072bah)		;a64e	3a ba 72 	: . r 
	ld b,a			;a651	47 	G 
	bit 6,a		;a652	cb 77 	. w 
	jr nz,$+11		;a654	20 09 	  . 
	ld a,(072bah)		;a656	3a ba 72 	: . r 
	set 5,a		;a659	cb ef 	. . 
	ld (072bah),a		;a65b	32 ba 72 	2 . r 
	inc e			;a65e	1c 	. 
	ld a,e			;a65f	7b 	{ 
	and a			;a660	a7 	. 
	ret			;a661	c9 	. 
	ld a,(0726eh)		;a662	3a 6e 72 	: n r 
	bit 1,a		;a665	cb 4f 	. O 
	ld a,(07274h)		;a667	3a 74 72 	: t r 
	jr z,$+5		;a66a	28 03 	( . 
	ld a,(07275h)		;a66c	3a 75 72 	: u r 
	cp 00bh		;a66f	fe 0b 	. . 
	jr c,$+6		;a671	38 04 	8 . 
	sub 00ah		;a673	d6 0a 	. . 
	jr $-6		;a675	18 f8 	. . 
	cp 004h		;a677	fe 04 	. . 
	jr nz,$+6		;a679	20 04 	  . 
	ld a,098h		;a67b	3e 98 	> . 
	jr $+4		;a67d	18 02 	. . 
	ld a,078h		;a67f	3e 78 	> x 
	ld (072beh),a		;a681	32 be 72 	2 . r 
	ld a,020h		;a684	3e 20 	>   
	ld (072bfh),a		;a686	32 bf 72 	2 . r 
	ld a,00ch		;a689	3e 0c 	> . 
	ld (072c2h),a		;a68b	32 c2 72 	2 . r 
	ld a,(072bah)		;a68e	3a ba 72 	: . r 
	set 6,a		;a691	cb f7 	. . 
	ld (072bah),a		;a693	32 ba 72 	2 . r 
	ld a,(07272h)		;a696	3a 72 72 	: r r 
	bit 5,a		;a699	cb 6f 	. o 
	jr nz,$+16		;a69b	20 0e 	  . 
	ld hl,072c4h		;a69d	21 c4 72 	! . r 
	set 0,(hl)		;a6a0	cb c6 	. . 
	ld hl,005a0h		;a6a2	21 a0 05 	! . . 
	call 01fcdh		;a6a5	cd cd 1f 	. . . 
	ld (0726fh),a		;a6a8	32 6f 72 	2 o r 
	ld a,(072bah)		;a6ab	3a ba 72 	: . r 
	bit 5,a		;a6ae	cb 6f 	. o 
	jr z,$+10		;a6b0	28 08 	( . 
	res 5,a		;a6b2	cb af 	. . 
	ld (072bah),a		;a6b4	32 ba 72 	2 . r 
	jp 0d31ch		;a6b7	c3 1c d3 	. . . 
	ret			;a6ba	c9 	. 
	push ix		;a6bb	dd e5 	. . 
	push iy		;a6bd	fd e5 	. . 
	ld a,(072c4h)		;a6bf	3a c4 72 	: . r 
	bit 0,a		;a6c2	cb 47 	. G 
	jr z,$+46		;a6c4	28 2c 	( , 
	call 0a61fh		;a6c6	cd 1f a6 	. . . 
	ld a,(0726fh)		;a6c9	3a 6f 72 	: o r 
	call 01fd0h		;a6cc	cd d0 1f 	. . . 
	and a			;a6cf	a7 	. 
	jr z,$+34		;a6d0	28 20 	(   
	ld hl,072c4h		;a6d2	21 c4 72 	! . r 
	res 0,(hl)		;a6d5	cb 86 	. . 
	ld a,040h		;a6d7	3e 40 	> @ 
	ld (072bdh),a		;a6d9	32 bd 72 	2 . r 
	ld a,001h		;a6dc	3e 01 	> . 
	ld (072c2h),a		;a6de	32 c2 72 	2 . r 
	ld a,(072bah)		;a6e1	3a ba 72 	: . r 
	res 6,a		;a6e4	cb b7 	. . 
	res 5,a		;a6e6	cb af 	. . 
	ld (072bah),a		;a6e8	32 ba 72 	2 . r 
	call 0ca24h		;a6eb	cd 24 ca 	. $ . 
	xor a			;a6ee	af 	. 
	jp 0a77eh		;a6ef	c3 7e a7 	. ~ . 
	ld iy,072bdh		;a6f2	fd 21 bd 72 	. ! . r 
	set 4,(iy+000h)		;a6f6	fd cb 00 e6 	. . . . 
	call 09f29h		;a6fa	cd 29 9f 	. ) . 
	ld d,a			;a6fd	57 	W 
	push de			;a6fe	d5 	. 
	ld hl,07272h		;a6ff	21 72 72 	! r r 
	bit 5,(hl)		;a702	cb 6e 	. n 
	jr z,$+7		;a704	28 05 	( . 
	res 5,(hl)		;a706	cb ae 	. . 
	call 0b8a3h		;a708	cd a3 b8 	. . . 
	call 0a527h		;a70b	cd 27 a5 	. ' . 
	pop de			;a70e	d1 	. 
	jr z,$+60		;a70f	28 3a 	( : 
	ld a,(0728ah)		;a711	3a 8a 72 	: . r 
	bit 4,a		;a714	cb 67 	. g 
	jr nz,$+53		;a716	20 33 	  3 
	ld a,(072c2h)		;a718	3a c2 72 	: . r 
	dec a			;a71b	3d 	= 
	ld (072c2h),a		;a71c	32 c2 72 	2 . r 
	jr nz,$+16		;a71f	20 0e 	  . 
	ld a,00ch		;a721	3e 0c 	> . 
	ld (072c2h),a		;a723	32 c2 72 	2 . r 
	call 01ffdh		;a726	cd fd 1f 	. . . 
	and 00fh		;a729	e6 0f 	. . 
	cp 007h		;a72b	fe 07 	. . 
	jr nc,$+62		;a72d	30 3c 	0 < 
	ld a,(072c1h)		;a72f	3a c1 72 	: . r 
	and 00fh		;a732	e6 0f 	. . 
	ld c,a			;a734	4f 	O 
	ld b,000h		;a735	06 00 	. . 
	ld hl,0a783h		;a737	21 83 a7 	! . . 
	add hl,bc			;a73a	09 	. 
	ld a,(hl)			;a73b	7e 	~ 
	and d			;a73c	a2 	. 
	jr z,$+46		;a73d	28 2c 	( , 
	ld a,(072c1h)		;a73f	3a c1 72 	: . r 
	and 00fh		;a742	e6 0f 	. . 
	call 09d2fh		;a744	cd 2f 9d 	. / . 
	jr z,$+52		;a747	28 32 	( 2 
	jr $+34		;a749	18 20 	.   
	ld a,(072bfh)		;a74b	3a bf 72 	: . r 
	ld b,a			;a74e	47 	G 
	ld a,(072beh)		;a74f	3a be 72 	: . r 
	ld c,a			;a752	4f 	O 
	push de			;a753	d5 	. 
	call 0ac3fh		;a754	cd 3f ac 	. ? . 
	pop bc			;a757	c1 	. 
	call 0a028h		;a758	cd 28 a0 	. ( . 
	jr z,$-67		;a75b	28 bb 	( . 
	cp 002h		;a75d	fe 02 	. . 
	jr z,$+12		;a75f	28 0a 	( . 
	ld a,(072c1h)		;a761	3a c1 72 	: . r 
	and 007h		;a764	e6 07 	. . 
	call 09d2fh		;a766	cd 2f 9d 	. / . 
	jr z,$+18		;a769	28 10 	( . 
	call 09f29h		;a76b	cd 29 9f 	. ) . 
	jr z,$+13		;a76e	28 0b 	( . 
	call 09e7ah		;a770	cd 7a 9e 	. z . 
	ld a,(072c1h)		;a773	3a c1 72 	: . r 
	and 007h		;a776	e6 07 	. . 
	call 09d2fh		;a778	cd 2f 9d 	. / . 
	call 09fc8h		;a77b	cd c8 9f 	. . . 
	pop iy		;a77e	fd e1 	. . 
	pop ix		;a780	dd e1 	. . 
	ret			;a782	c9 	. 
	nop			;a783	00 	. 
	ld b,b			;a784	40 	@ 
	add a,b			;a785	80 	. 
	djnz $+34		;a786	10 20 	.   
	ld a,(07272h)		;a788	3a 72 72 	: r r 
	bit 4,a		;a78b	cb 67 	. g 
	jr z,$+9		;a78d	28 07 	( . 
	ld a,(072bah)		;a78f	3a ba 72 	: . r 
	bit 6,a		;a792	cb 77 	. w 
	jr z,$+71		;a794	28 45 	( E 
	ld a,(0726eh)		;a796	3a 6e 72 	: n r 
	bit 1,a		;a799	cb 4f 	. O 
	ld ix,072b8h		;a79b	dd 21 b8 72 	. ! . r 
	jr z,$+6		;a79f	28 04 	( . 
	ld ix,072b9h		;a7a1	dd 21 b9 72 	. ! . r 
	ld a,(072bah)		;a7a5	3a ba 72 	: . r 
	and 007h		;a7a8	e6 07 	. . 
	ld hl,0a7dch		;a7aa	21 dc a7 	! . . 
	ld c,a			;a7ad	4f 	O 
	add a,a			;a7ae	87 	. 
	add a,c			;a7af	81 	. 
	ld c,a			;a7b0	4f 	O 
	ld b,000h		;a7b1	06 00 	. . 
	add hl,bc			;a7b3	09 	. 
	ld a,(hl)			;a7b4	7e 	~ 
	inc hl			;a7b5	23 	# 
	and (ix+000h)		;a7b6	dd a6 00 	. . . 
	jr z,$+3		;a7b9	28 01 	( . 
	inc hl			;a7bb	23 	# 
	ld d,(hl)			;a7bc	56 	V 
	ld a,(072bah)		;a7bd	3a ba 72 	: . r 
	bit 5,a		;a7c0	cb 6f 	. o 
	jr z,$+6		;a7c2	28 04 	( . 
	res 5,a		;a7c4	cb af 	. . 
	jr $+5		;a7c6	18 03 	. . 
	set 5,a		;a7c8	cb ef 	. . 
	inc d			;a7ca	14 	. 
	ld (072bah),a		;a7cb	32 ba 72 	2 . r 
	ld a,(072bfh)		;a7ce	3a bf 72 	: . r 
	ld b,a			;a7d1	47 	G 
	ld a,(072beh)		;a7d2	3a be 72 	: . r 
	ld c,a			;a7d5	4f 	O 
	ld a,003h		;a7d6	3e 03 	> . 
	call 0b629h		;a7d8	cd 29 b6 	. ) . 
	ret			;a7db	c9 	. 
	ld bc,00c01h		;a7dc	01 01 0c 	. . . 
	ld (bc),a			;a7df	02 	. 
	inc bc			;a7e0	03 	. 
	ld c,004h		;a7e1	0e 04 	. . 
	dec b			;a7e3	05 	. 
	djnz $+10		;a7e4	10 08 	. . 
	rlca			;a7e6	07 	. 
	ld (de),a			;a7e7	12 	. 
	djnz $+11		;a7e8	10 09 	. . 
	inc d			;a7ea	14 	. 
	ex af,af'			;a7eb	08 	. 
	rlca			;a7ec	07 	. 
	ld (de),a			;a7ed	12 	. 
	inc b			;a7ee	04 	. 
	dec b			;a7ef	05 	. 
	djnz $+4		;a7f0	10 02 	. . 
	inc bc			;a7f2	03 	. 
	ld c,03ah		;a7f3	0e 3a 	. : 
	push bc			;a7f5	c5 	. 
	ld (hl),d			;a7f6	72 	r 
	and 003h		;a7f7	e6 03 	. . 
	ld iy,072c7h		;a7f9	fd 21 c7 72 	. ! . r 
	ld bc,00006h		;a7fd	01 06 00 	. . . 
	dec a			;a800	3d 	= 
	jp m,0a808h		;a801	fa 08 a8 	. . . 
	add iy,bc		;a804	fd 09 	. . 
	jr $-6		;a806	18 f8 	. . 
	bit 7,(iy+004h)		;a808	fd cb 04 7e 	. . . ~ 
	jr z,$+31		;a80c	28 1d 	( . 
	bit 7,(iy+000h)		;a80e	fd cb 00 7e 	. . . ~ 
	jr nz,$+25		;a812	20 17 	  . 
	ld a,(iy+003h)		;a814	fd 7e 03 	. ~ . 
	call 01fd0h		;a817	cd d0 1f 	. . . 
	and a			;a81a	a7 	. 
	jr z,$+16		;a81b	28 0e 	( . 
	call 0a83eh		;a81d	cd 3e a8 	. > . 
	call 0a8cbh		;a820	cd cb a8 	. . . 
	call 0a921h		;a823	cd 21 a9 	. ! . 
	call 0a92ch		;a826	cd 2c a9 	. , . 
	jr $+3		;a829	18 01 	. . 
	xor a			;a82b	af 	. 
	push af			;a82c	f5 	. 
	ld hl,072c5h		;a82d	21 c5 72 	! . r 
	inc (hl)			;a830	34 	4 
	ld a,(hl)			;a831	7e 	~ 
	and 003h		;a832	e6 03 	. . 
	cp 003h		;a834	fe 03 	. . 
	jr nz,$+6		;a836	20 04 	  . 
	ld a,(hl)			;a838	7e 	~ 
	and 0fch		;a839	e6 fc 	. . 
	ld (hl),a			;a83b	77 	w 
	pop af			;a83c	f1 	. 
	ret			;a83d	c9 	. 
	jp 0d383h		;a83e	c3 83 d3 	. . . 
	bit 0,a		;a841	cb 47 	. G 
	jr nz,$+16		;a843	20 0e 	  . 
	ld a,(072c6h)		;a845	3a c6 72 	: . r 
	call 01fd0h		;a848	cd d0 1f 	. . . 
	and a			;a84b	a7 	. 
	jr z,$+12		;a84c	28 0a 	( . 
	ld hl,072c3h		;a84e	21 c3 72 	! . r 
	set 0,(hl)		;a851	cb c6 	. . 
	call 0a460h		;a853	cd 60 a4 	. ` . 
	jr $+112		;a856	18 6e 	. n 
	ld a,(iy+002h)		;a858	fd 7e 02 	. ~ . 
	and 00fh		;a85b	e6 0f 	. . 
	jr nz,$+11		;a85d	20 09 	  . 
	ld a,(iy+001h)		;a85f	fd 7e 01 	. ~ . 
	and 00fh		;a862	e6 0f 	. . 
	cp 008h		;a864	fe 08 	. . 
	jr z,$+18		;a866	28 10 	( . 
	ld a,(iy+004h)		;a868	fd 7e 04 	. ~ . 
	and 007h		;a86b	e6 07 	. . 
	dec a			;a86d	3d 	= 
	ld e,a			;a86e	5f 	_ 
	ld d,000h		;a86f	16 00 	. . 
	ld hl,0a8c7h		;a871	21 c7 a8 	! . . 
	add hl,de			;a874	19 	. 
	ld h,(hl)			;a875	66 	f 
	jr $+34		;a876	18 20 	.   
	ld h,0f0h		;a878	26 f0 	& . 
	ld a,(iy+002h)		;a87a	fd 7e 02 	. ~ . 
	cp 028h		;a87d	fe 28 	. ( 
	jr nc,$+4		;a87f	30 02 	0 . 
	res 4,h		;a881	cb a4 	. . 
	cp 0a8h		;a883	fe a8 	. . 
	jr c,$+4		;a885	38 02 	8 . 
	res 5,h		;a887	cb ac 	. . 
	ld a,(iy+001h)		;a889	fd 7e 01 	. ~ . 
	cp 020h		;a88c	fe 20 	.   
	jr nc,$+4		;a88e	30 02 	0 . 
	res 7,h		;a890	cb bc 	. . 
	cp 0e0h		;a892	fe e0 	. . 
	jr c,$+4		;a894	38 02 	8 . 
	res 6,h		;a896	cb b4 	. . 
	ld a,h			;a898	7c 	| 
	push hl			;a899	e5 	. 
	call 09e7ah		;a89a	cd 7a 9e 	. z . 
	ld a,(iy+004h)		;a89d	fd 7e 04 	. ~ . 
	and 007h		;a8a0	e6 07 	. . 
	call 09d2fh		;a8a2	cd 2f 9d 	. / . 
	pop hl			;a8a5	e1 	. 
	jr z,$+32		;a8a6	28 1e 	( . 
	ld a,(iy+004h)		;a8a8	fd 7e 04 	. ~ . 
	jp 0d3d5h		;a8ab	c3 d5 d3 	. . . 
	nop			;a8ae	00 	. 
	jr nc,$+4		;a8af	30 02 	0 . 
	ld c,030h		;a8b1	0e 30 	. 0 
	ld a,h			;a8b3	7c 	| 
	and c			;a8b4	a1 	. 
	ld h,a			;a8b5	67 	g 
	jr nz,$-30		;a8b6	20 e0 	  . 
	ld a,(iy+004h)		;a8b8	fd 7e 04 	. ~ . 
	bit 0,a		;a8bb	cb 47 	. G 
	jr z,$+5		;a8bd	28 03 	( . 
	inc a			;a8bf	3c 	< 
	jr $+3		;a8c0	18 01 	. . 
	dec a			;a8c2	3d 	= 
	ld (iy+004h),a		;a8c3	fd 77 04 	. w . 
	ret			;a8c6	c9 	. 
	ld b,b			;a8c7	40 	@ 
	add a,b			;a8c8	80 	. 
	djnz $+34		;a8c9	10 20 	.   
	call 09b4fh		;a8cb	cd 4f 9b 	. O . 
	ld b,(iy+002h)		;a8ce	fd 46 02 	. F . 
	ld c,(iy+001h)		;a8d1	fd 4e 01 	. N . 
	call 0ac3fh		;a8d4	cd 3f ac 	. ? . 
	ld d,a			;a8d7	57 	W 
	call 0b173h		;a8d8	cd 73 b1 	. s . 
	ld d,001h		;a8db	16 01 	. . 
	ld a,(iy+004h)		;a8dd	fd 7e 04 	. ~ . 
	and 007h		;a8e0	e6 07 	. . 
	cp 001h		;a8e2	fe 01 	. . 
	jr z,$+33		;a8e4	28 1f 	( . 
	cp 002h		;a8e6	fe 02 	. . 
	jr nz,$+6		;a8e8	20 04 	  . 
	inc d			;a8ea	14 	. 
	inc d			;a8eb	14 	. 
	jr $+25		;a8ec	18 17 	. . 
	ld a,(072c5h)		;a8ee	3a c5 72 	: . r 
	add a,a			;a8f1	87 	. 
	add a,a			;a8f2	87 	. 
	ld c,a			;a8f3	4f 	O 
	ld b,000h		;a8f4	06 00 	. . 
	ld hl,0712fh		;a8f6	21 2f 71 	! / q 
	add hl,bc			;a8f9	09 	. 
	ld a,(hl)			;a8fa	7e 	~ 
	cp 0e0h		;a8fb	fe e0 	. . 
	jr z,$+8		;a8fd	28 06 	( . 
	cp 0e4h		;a8ff	fe e4 	. . 
	jr z,$+4		;a901	28 02 	( . 
	inc d			;a903	14 	. 
	inc d			;a904	14 	. 
	ld a,(iy+005h)		;a905	fd 7e 05 	. ~ . 
	bit 7,a		;a908	cb 7f 	.  
	jr z,$+3		;a90a	28 01 	( . 
	inc d			;a90c	14 	. 
	xor 080h		;a90d	ee 80 	. . 
	ld (iy+005h),a		;a90f	fd 77 05 	. w . 
	ld b,(iy+002h)		;a912	fd 46 02 	. F . 
	ld c,(iy+001h)		;a915	fd 4e 01 	. N . 
	ld a,(072c5h)		;a918	3a c5 72 	: . r 
	add a,011h		;a91b	c6 11 	. . 
	call 0b629h		;a91d	cd 29 b6 	. ) . 
	ret			;a920	c9 	. 
	call 09be2h		;a921	cd e2 9b 	. . . 
	xor a			;a924	af 	. 
	call 01fcdh		;a925	cd cd 1f 	. . . 
	ld (iy+003h),a		;a928	fd 77 03 	. w . 
	ret			;a92b	c9 	. 
	call 09fc8h		;a92c	cd c8 9f 	. . . 
	ret			;a92f	c9 	. 
	nop			;a930	00 	. 
	ld hl,07273h		;a931	21 73 72 	! s r 
	ld (hl),000h		;a934	36 00 	6 . 
	cp 001h		;a936	fe 01 	. . 
	jr nz,$+21		;a938	20 13 	  . 
	ld hl,00078h		;a93a	21 78 00 	! x . 
	xor a			;a93d	af 	. 
	call 01fcdh		;a93e	cd cd 1f 	. . . 
	push af			;a941	f5 	. 
	pop af			;a942	f1 	. 
	push af			;a943	f5 	. 
	call 01fd0h		;a944	cd d0 1f 	. . . 
	and a			;a947	a7 	. 
	jr z,$-6		;a948	28 f8 	( . 
	pop af			;a94a	f1 	. 
	jr $+40		;a94b	18 26 	. & 
	push af			;a94d	f5 	. 
	ld hl,0001eh		;a94e	21 1e 00 	! . . 
	xor a			;a951	af 	. 
	call 01fcdh		;a952	cd cd 1f 	. . . 
	push af			;a955	f5 	. 
	pop af			;a956	f1 	. 
	push af			;a957	f5 	. 
	call 01fd0h		;a958	cd d0 1f 	. . . 
	and a			;a95b	a7 	. 
	jr z,$-6		;a95c	28 f8 	( . 
	pop af			;a95e	f1 	. 
	pop af			;a95f	f1 	. 
	cp 002h		;a960	fe 02 	. . 
	jr nz,$+7		;a962	20 05 	  . 
	call 0a988h		;a964	cd 88 a9 	. . . 
	jr $+5		;a967	18 03 	. . 
	call 0a99ch		;a969	cd 9c a9 	. . . 
	call 0aa25h		;a96c	cd 25 aa 	. % . 
	ld a,002h		;a96f	3e 02 	> . 
	jr $+22		;a971	18 14 	. . 
	call 0aa69h		;a973	cd 69 aa 	. i . 
	cp 001h		;a976	fe 01 	. . 
	jr z,$+15		;a978	28 0d 	( . 
	and a			;a97a	a7 	. 
	jr z,$+9		;a97b	28 07 	( . 
	call 0aadch		;a97d	cd dc aa 	. . . 
	ld a,001h		;a980	3e 01 	> . 
	jr $+5		;a982	18 03 	. . 
	call 0ab28h		;a984	cd 28 ab 	. ( . 
	ret			;a987	c9 	. 
	call 0ca0ah		;a988	cd 0a ca 	. . . 
	ld hl,00103h		;a98b	21 03 01 	! . . 
	call 01fcdh		;a98e	cd cd 1f 	. . . 
	push af			;a991	f5 	. 
	pop af			;a992	f1 	. 
	push af			;a993	f5 	. 
	call 01fd0h		;a994	cd d0 1f 	. . . 
	and a			;a997	a7 	. 
	jr z,$-6		;a998	28 f8 	( . 
	pop af			;a99a	f1 	. 
	ret			;a99b	c9 	. 
	ld hl,0726eh		;a99c	21 6e 72 	! n r 
	set 7,(hl)		;a99f	cb fe 	. . 
	bit 7,(hl)		;a9a1	cb 7e 	. ~ 
	jr nz,$-2		;a9a3	20 fc 	  . 
	ld hl,01000h		;a9a5	21 00 10 	! . . 
	ld de,00300h		;a9a8	11 00 03 	. . . 
	ld a,000h		;a9ab	3e 00 	> . 
	call 01f82h		;a9ad	cd 82 1f 	. . . 
	ld hl,01900h		;a9b0	21 00 19 	! . . 
	ld de,00080h		;a9b3	11 80 00 	. . . 
	ld a,000h		;a9b6	3e 00 	> . 
	call 01f82h		;a9b8	cd 82 1f 	. . . 
	ld hl,070e9h		;a9bb	21 e9 70 	! . p 
	ld b,050h		;a9be	06 50 	. P 
	ld (hl),000h		;a9c0	36 00 	6 . 
	inc hl			;a9c2	23 	# 
	djnz $-3		;a9c3	10 fb 	. . 
	ld a,006h		;a9c5	3e 06 	> . 
	call 0ae2fh		;a9c7	cd 2f ae 	. / . 
	ld bc,0070ch		;a9ca	01 0c 07 	. . . 
	call 01fd9h		;a9cd	cd d9 1f 	. . . 
	xor a			;a9d0	af 	. 
	ld (072bch),a		;a9d1	32 bc 72 	2 . r 
	ld (072bbh),a		;a9d4	32 bb 72 	2 . r 
	ld hl,0726eh		;a9d7	21 6e 72 	! n r 
	bit 1,(hl)		;a9da	cb 4e 	. N 
	jr nz,$+10		;a9dc	20 08 	  . 
	ld (072b8h),a		;a9de	32 b8 72 	2 . r 
	ld hl,07276h		;a9e1	21 76 72 	! v r 
	jr $+8		;a9e4	18 06 	. . 
	ld (072b9h),a		;a9e6	32 b9 72 	2 . r 
	ld hl,07277h		;a9e9	21 77 72 	! w r 
	ld a,(hl)			;a9ec	7e 	~ 
	cp 006h		;a9ed	fe 06 	. . 
	jr nc,$+3		;a9ef	30 01 	0 . 
	inc (hl)			;a9f1	34 	4 
	ld bc,001e2h		;a9f2	01 e2 01 	. . . 
	call 01fd9h		;a9f5	cd d9 1f 	. . . 
	call 0c958h		;a9f8	cd 58 c9 	. X . 
	call 0ca00h		;a9fb	cd 00 ca 	. . . 
	ld hl,00180h		;a9fe	21 80 01 	! . . 
	xor a			;aa01	af 	. 
	call 01fcdh		;aa02	cd cd 1f 	. . . 
	push af			;aa05	f5 	. 
	pop af			;aa06	f1 	. 
	push af			;aa07	f5 	. 
	call 01fd0h		;aa08	cd d0 1f 	. . . 
	and a			;aa0b	a7 	. 
	jr z,$-6		;aa0c	28 f8 	( . 
	pop af			;aa0e	f1 	. 
	ld hl,0726eh		;aa0f	21 6e 72 	! n r 
	set 7,(hl)		;aa12	cb fe 	. . 
	bit 7,(hl)		;aa14	cb 7e 	. ~ 
	jr nz,$-2		;aa16	20 fc 	  . 
	ld bc,00700h		;aa18	01 00 07 	. . . 
	call 01fd9h		;aa1b	cd d9 1f 	. . . 
	ld bc,001e2h		;aa1e	01 e2 01 	. . . 
	call 01fd9h		;aa21	cd d9 1f 	. . . 
	ret			;aa24	c9 	. 
	ld hl,0726eh		;aa25	21 6e 72 	! n r 
	set 7,(hl)		;aa28	cb fe 	. . 
	bit 7,(hl)		;aa2a	cb 7e 	. ~ 
	jr nz,$-2		;aa2c	20 fc 	  . 
	ld hl,07274h		;aa2e	21 74 72 	! t r 
	ld ix,07278h		;aa31	dd 21 78 72 	. ! x r 
	ld a,(0726eh)		;aa35	3a 6e 72 	: n r 
	bit 1,a		;aa38	cb 4f 	. O 
	jr z,$+9		;aa3a	28 07 	( . 
	ld hl,07275h		;aa3c	21 75 72 	! u r 
	ld ix,07279h		;aa3f	dd 21 79 72 	. ! y r 
	ld (ix+000h),007h		;aa43	dd 36 00 07 	. 6 . . 
	inc (hl)			;aa47	34 	4 
	ld a,(hl)			;aa48	7e 	~ 
	call 0b286h		;aa49	cd 86 b2 	. . . 
	ld hl,0718ah		;aa4c	21 8a 71 	! . q 
	ld de,03400h		;aa4f	11 00 34 	. . 4 
	ld a,(0726eh)		;aa52	3a 6e 72 	: n r 
	bit 1,a		;aa55	cb 4f 	. O 
	jr z,$+5		;aa57	28 03 	( . 
	ld de,03600h		;aa59	11 00 36 	. . 6 
	ld bc,000d4h		;aa5c	01 d4 00 	. . . 
	call 01fdfh		;aa5f	cd df 1f 	. . . 
	ld bc,001e2h		;aa62	01 e2 01 	. . . 
	call 01fd9h		;aa65	cd d9 1f 	. . . 
	ret			;aa68	c9 	. 
	ld hl,0726eh		;aa69	21 6e 72 	! n r 
	set 7,(hl)		;aa6c	cb fe 	. . 
	bit 7,(hl)		;aa6e	cb 7e 	. ~ 
	jr nz,$-2		;aa70	20 fc 	  . 
	ld de,03400h		;aa72	11 00 34 	. . 4 
	bit 1,(hl)		;aa75	cb 4e 	. N 
	jr z,$+5		;aa77	28 03 	( . 
	ld de,03600h		;aa79	11 00 36 	. . 6 
	ld hl,0718ah		;aa7c	21 8a 71 	! . q 
	ld bc,000d4h		;aa7f	01 d4 00 	. . . 
	call 01fdfh		;aa82	cd df 1f 	. . . 
	ld bc,001e2h		;aa85	01 e2 01 	. . . 
	call 01fd9h		;aa88	cd d9 1f 	. . . 
	ld ix,07276h		;aa8b	dd 21 76 72 	. ! v r 
	ld iy,07277h		;aa8f	fd 21 77 72 	. ! w r 
	ld hl,0726eh		;aa93	21 6e 72 	! n r 
	bit 1,(hl)		;aa96	cb 4e 	. N 
	jr nz,$+37		;aa98	20 23 	  # 
	dec (ix+000h)		;aa9a	dd 35 00 	. 5 . 
	jr z,$+16		;aa9d	28 0e 	( . 
	bit 0,(hl)		;aa9f	cb 46 	. F 
	jr z,$+41		;aaa1	28 27 	( ' 
	ld a,(iy+000h)		;aaa3	fd 7e 00 	. ~ . 
	and a			;aaa6	a7 	. 
	jr z,$+35		;aaa7	28 21 	( ! 
	set 1,(hl)		;aaa9	cb ce 	. . 
	jr $+31		;aaab	18 1d 	. . 
	bit 0,(hl)		;aaad	cb 46 	. F 
	jr z,$+43		;aaaf	28 29 	( ) 
	ld a,(iy+000h)		;aab1	fd 7e 00 	. ~ . 
	and a			;aab4	a7 	. 
	jr z,$+37		;aab5	28 23 	( # 
	set 1,(hl)		;aab7	cb ce 	. . 
	ld a,002h		;aab9	3e 02 	> . 
	jr $+32		;aabb	18 1e 	. . 
	dec (iy+000h)		;aabd	fd 35 00 	. 5 . 
	jr z,$+14		;aac0	28 0c 	( . 
	ld a,(ix+000h)		;aac2	dd 7e 00 	. ~ . 
	and a			;aac5	a7 	. 
	jr z,$+4		;aac6	28 02 	( . 
	res 1,(hl)		;aac8	cb 8e 	. . 
	ld a,001h		;aaca	3e 01 	> . 
	jr $+15		;aacc	18 0d 	. . 
	ld a,(ix+000h)		;aace	dd 7e 00 	. ~ . 
	and a			;aad1	a7 	. 
	jr z,$+8		;aad2	28 06 	( . 
	res 1,(hl)		;aad4	cb 8e 	. . 
	ld a,003h		;aad6	3e 03 	> . 
	jr $+3		;aad8	18 01 	. . 
	xor a			;aada	af 	. 
	ret			;aadb	c9 	. 
	push af			;aadc	f5 	. 
	ld hl,0726eh		;aadd	21 6e 72 	! n r 
	set 7,(hl)		;aae0	cb fe 	. . 
	bit 7,(hl)		;aae2	cb 7e 	. ~ 
	jr nz,$-2		;aae4	20 fc 	  . 
	ld hl,01000h		;aae6	21 00 10 	! . . 
	ld de,00300h		;aae9	11 00 03 	. . . 
	xor a			;aaec	af 	. 
	call 01f82h		;aaed	cd 82 1f 	. . . 
	ld hl,01900h		;aaf0	21 00 19 	! . . 
	ld de,00080h		;aaf3	11 80 00 	. . . 
	xor a			;aaf6	af 	. 
	call 01f82h		;aaf7	cd 82 1f 	. . . 
	ld hl,070e9h		;aafa	21 e9 70 	! . p 
	ld b,050h		;aafd	06 50 	. P 
	ld (hl),000h		;aaff	36 00 	6 . 
	inc hl			;ab01	23 	# 
	djnz $-3		;ab02	10 fb 	. . 
	pop af			;ab04	f1 	. 
	cp 002h		;ab05	fe 02 	. . 
	ld a,007h		;ab07	3e 07 	> . 
	jr z,$+4		;ab09	28 02 	( . 
	ld a,008h		;ab0b	3e 08 	> . 
	call 0ae2fh		;ab0d	cd 2f ae 	. / . 
	ld bc,001e2h		;ab10	01 e2 01 	. . . 
	call 01fd9h		;ab13	cd d9 1f 	. . . 
	xor a			;ab16	af 	. 
	ld hl,000b4h		;ab17	21 b4 00 	! . . 
	call 01fcdh		;ab1a	cd cd 1f 	. . . 
	push af			;ab1d	f5 	. 
	pop af			;ab1e	f1 	. 
	push af			;ab1f	f5 	. 
	call 01fd0h		;ab20	cd d0 1f 	. . . 
	and a			;ab23	a7 	. 
	jr z,$-6		;ab24	28 f8 	( . 
	pop af			;ab26	f1 	. 
	ret			;ab27	c9 	. 
	ld hl,0726eh		;ab28	21 6e 72 	! n r 
	set 7,(hl)		;ab2b	cb fe 	. . 
	bit 7,(hl)		;ab2d	cb 7e 	. ~ 
	jr nz,$-2		;ab2f	20 fc 	  . 
	ld hl,01900h		;ab31	21 00 19 	! . . 
	ld de,00080h		;ab34	11 80 00 	. . . 
	xor a			;ab37	af 	. 
	call 01f82h		;ab38	cd 82 1f 	. . . 
	ld hl,070e9h		;ab3b	21 e9 70 	! . p 
	ld b,050h		;ab3e	06 50 	. P 
	ld (hl),000h		;ab40	36 00 	6 . 
	inc hl			;ab42	23 	# 
	djnz $-3		;ab43	10 fb 	. . 
	ld a,009h		;ab45	3e 09 	> . 
	call 0ae2fh		;ab47	cd 2f ae 	. / . 
	ld bc,001e2h		;ab4a	01 e2 01 	. . . 
	call 01fd9h		;ab4d	cd d9 1f 	. . . 
	call 0c9f3h		;ab50	cd f3 c9 	. . . 
	ld hl,00168h		;ab53	21 68 01 	! h . 
	xor a			;ab56	af 	. 
	call 01fcdh		;ab57	cd cd 1f 	. . . 
	push af			;ab5a	f5 	. 
	pop af			;ab5b	f1 	. 
	push af			;ab5c	f5 	. 
	call 01fd0h		;ab5d	cd d0 1f 	. . . 
	and a			;ab60	a7 	. 
	jr z,$-6		;ab61	28 f8 	( . 
	pop af			;ab63	f1 	. 
	ld hl,004b0h		;ab64	21 b0 04 	! . . 
	xor a			;ab67	af 	. 
	call 01fcdh		;ab68	cd cd 1f 	. . . 
	push af			;ab6b	f5 	. 
	ld a,(0708ch)		;ab6c	3a 8c 70 	: . p 
	cp 00ah		;ab6f	fe 0a 	. . 
	jr z,$+52		;ab71	28 32 	( 2 
	cp 00bh		;ab73	fe 0b 	. . 
	jr z,$+52		;ab75	28 32 	( 2 
	ld a,(07091h)		;ab77	3a 91 70 	: . p 
	cp 00ah		;ab7a	fe 0a 	. . 
	jr z,$+41		;ab7c	28 27 	( ' 
	cp 00bh		;ab7e	fe 0b 	. . 
	jr z,$+41		;ab80	28 27 	( ' 
	pop af			;ab82	f1 	. 
	push af			;ab83	f5 	. 
	call 01fd0h		;ab84	cd d0 1f 	. . . 
	and a			;ab87	a7 	. 
	jr z,$-28		;ab88	28 e2 	( . 
	ld hl,0726eh		;ab8a	21 6e 72 	! n r 
	set 7,(hl)		;ab8d	cb fe 	. . 
	bit 7,(hl)		;ab8f	cb 7e 	. ~ 
	jr nz,$-2		;ab91	20 fc 	  . 
	ld hl,01000h		;ab93	21 00 10 	! . . 
	ld de,00300h		;ab96	11 00 03 	. . . 
	xor a			;ab99	af 	. 
	call 01f82h		;ab9a	cd 82 1f 	. . . 
	ld bc,001e2h		;ab9d	01 e2 01 	. . . 
	call 01fd9h		;aba0	cd d9 1f 	. . . 
	jr $-55		;aba3	18 c7 	. . 
	pop af			;aba5	f1 	. 
	xor a			;aba6	af 	. 
	jr $+14		;aba7	18 0c 	. . 
	ld hl,0726eh		;aba9	21 6e 72 	! n r 
	set 7,(hl)		;abac	cb fe 	. . 
	bit 7,(hl)		;abae	cb 7e 	. ~ 
	jr nz,$-2		;abb0	20 fc 	  . 
	pop af			;abb2	f1 	. 
	ld a,003h		;abb3	3e 03 	> . 
	ret			;abb5	c9 	. 
	nop			;abb6	00 	. 
	ld b,020h		;abb7	06 20 	.   
	ld c,008h		;abb9	0e 08 	. . 
	ld d,000h		;abbb	16 00 	. . 
	dec a			;abbd	3d 	= 
	cp 010h		;abbe	fe 10 	. . 
	jr c,$+7		;abc0	38 05 	8 . 
	sub 010h		;abc2	d6 10 	. . 
	inc d			;abc4	14 	. 
	jr $-7		;abc5	18 f7 	. . 
	ld e,a			;abc7	5f 	_ 
	ld a,e			;abc8	7b 	{ 
	cp 000h		;abc9	fe 00 	. . 
	jr z,$+9		;abcb	28 07 	( . 
	ld a,c			;abcd	79 	y 
	add a,010h		;abce	c6 10 	. . 
	ld c,a			;abd0	4f 	O 
	dec e			;abd1	1d 	. 
	jr $-10		;abd2	18 f4 	. . 
	ld a,d			;abd4	7a 	z 
	cp 000h		;abd5	fe 00 	. . 
	jr z,$+9		;abd7	28 07 	( . 
	ld a,b			;abd9	78 	x 
	add a,010h		;abda	c6 10 	. . 
	ld b,a			;abdc	47 	G 
	dec d			;abdd	15 	. 
	jr $-22		;abde	18 e8 	. . 
	ret			;abe0	c9 	. 
	push ix		;abe1	dd e5 	. . 
	call 0ac1fh		;abe3	cd 1f ac 	. . . 
	ld ix,0ac2fh		;abe6	dd 21 2f ac 	. ! / . 
	ld e,a			;abea	5f 	_ 
	add ix,de		;abeb	dd 19 	. . 
	ld e,(ix+000h)		;abed	dd 5e 00 	. ^ . 
	ld a,(hl)			;abf0	7e 	~ 
	or e			;abf1	b3 	. 
	ld (hl),a			;abf2	77 	w 
	pop ix		;abf3	dd e1 	. . 
	ret			;abf5	c9 	. 
	push ix		;abf6	dd e5 	. . 
	call 0ac1fh		;abf8	cd 1f ac 	. . . 
	ld ix,0ac37h		;abfb	dd 21 37 ac 	. ! 7 . 
	ld e,a			;abff	5f 	_ 
	add ix,de		;ac00	dd 19 	. . 
	ld e,(ix+000h)		;ac02	dd 5e 00 	. ^ . 
	ld a,(hl)			;ac05	7e 	~ 
	and e			;ac06	a3 	. 
	ld (hl),a			;ac07	77 	w 
	pop ix		;ac08	dd e1 	. . 
	ret			;ac0a	c9 	. 
	push ix		;ac0b	dd e5 	. . 
	call 0ac1fh		;ac0d	cd 1f ac 	. . . 
	ld ix,0ac2fh		;ac10	dd 21 2f ac 	. ! / . 
	ld e,a			;ac14	5f 	_ 
	add ix,de		;ac15	dd 19 	. . 
	ld e,(ix+000h)		;ac17	dd 5e 00 	. ^ . 
	ld a,(hl)			;ac1a	7e 	~ 
	and e			;ac1b	a3 	. 
	pop ix		;ac1c	dd e1 	. . 
	ret			;ac1e	c9 	. 
	ld e,000h		;ac1f	1e 00 	. . 
	dec a			;ac21	3d 	= 
	cp 008h		;ac22	fe 08 	. . 
	jr c,$+7		;ac24	38 05 	8 . 
	sub 008h		;ac26	d6 08 	. . 
	inc e			;ac28	1c 	. 
	jr $-7		;ac29	18 f7 	. . 
	ld d,000h		;ac2b	16 00 	. . 
	add hl,de			;ac2d	19 	. 
	ret			;ac2e	c9 	. 
	add a,b			;ac2f	80 	. 
	ld b,b			;ac30	40 	@ 
	jr nz,$+18		;ac31	20 10 	  . 
	ex af,af'			;ac33	08 	. 
	inc b			;ac34	04 	. 
	ld (bc),a			;ac35	02 	. 
	ld bc,0bf7fh		;ac36	01 7f bf 	.  . 
	rst 18h			;ac39	df 	. 
	rst 28h			;ac3a	ef 	. 
	rst 30h			;ac3b	f7 	. 
	ei			;ac3c	fb 	. 
	defb 0fdh,0feh,0c5h	;illegal sequence		;ac3d	fd fe c5 	. . . 
	ld d,001h		;ac40	16 01 	. . 
	ld a,b			;ac42	78 	x 
	sub 018h		;ac43	d6 18 	. . 
	sub 010h		;ac45	d6 10 	. . 
	jr c,$+10		;ac47	38 08 	8 . 
	push af			;ac49	f5 	. 
	ld a,d			;ac4a	7a 	z 
	add a,010h		;ac4b	c6 10 	. . 
	ld d,a			;ac4d	57 	W 
	pop af			;ac4e	f1 	. 
	jr $-10		;ac4f	18 f4 	. . 
	ld a,c			;ac51	79 	y 
	sub 010h		;ac52	d6 10 	. . 
	jr c,$+5		;ac54	38 03 	8 . 
	inc d			;ac56	14 	. 
	jr $-5		;ac57	18 f9 	. . 
	ld a,d			;ac59	7a 	z 
	dec a			;ac5a	3d 	= 
	ld b,000h		;ac5b	06 00 	. . 
	ld c,a			;ac5d	4f 	O 
	ld ix,0718ah		;ac5e	dd 21 8a 71 	. ! . q 
	add ix,bc		;ac62	dd 09 	. . 
	ld a,d			;ac64	7a 	z 
	pop bc			;ac65	c1 	. 
	ret			;ac66	c9 	. 
	ld a,(0726eh)		;ac67	3a 6e 72 	: n r 
	bit 1,a		;ac6a	cb 4f 	. O 
	jr nz,$+7		;ac6c	20 05 	  . 
	ld a,(07274h)		;ac6e	3a 74 72 	: t r 
	jr $+5		;ac71	18 03 	. . 
	ld a,(07275h)		;ac73	3a 75 72 	: u r 
	cp 00bh		;ac76	fe 0b 	. . 
	jr c,$+6		;ac78	38 04 	8 . 
	sub 00ah		;ac7a	d6 0a 	. . 
	jr $-6		;ac7c	18 f8 	. . 
	dec a			;ac7e	3d 	= 
	add a,a			;ac7f	87 	. 
	ld b,000h		;ac80	06 00 	. . 
	ld c,a			;ac82	4f 	O 
	call 01ffdh		;ac83	cd fd 1f 	. . . 
	bit 0,a		;ac86	cb 47 	. G 
	jr nz,$+8		;ac88	20 06 	  . 
	ld ix,0b961h		;ac8a	dd 21 61 b9 	. ! a . 
	jr $+6		;ac8e	18 04 	. . 
	ld ix,0b9b1h		;ac90	dd 21 b1 b9 	. ! . . 
	add ix,bc		;ac94	dd 09 	. . 
	ld l,(ix+000h)		;ac96	dd 6e 00 	. n . 
	ld h,(ix+001h)		;ac99	dd 66 01 	. f . 
	ld ix,0722ch		;ac9c	dd 21 2c 72 	. ! , r 
	ld d,005h		;aca0	16 05 	. . 
	ld a,(hl)			;aca2	7e 	~ 
	call 0abb7h		;aca3	cd b7 ab 	. . . 
	ld (ix+000h),080h		;aca6	dd 36 00 80 	. 6 . . 
	ld (ix+001h),b		;acaa	dd 70 01 	. p . 
	ld (ix+002h),c		;acad	dd 71 02 	. q . 
	ld (ix+003h),000h		;acb0	dd 36 03 00 	. 6 . . 
	inc hl			;acb4	23 	# 
	inc ix		;acb5	dd 23 	. # 
	inc ix		;acb7	dd 23 	. # 
	inc ix		;acb9	dd 23 	. # 
	inc ix		;acbb	dd 23 	. # 
	dec d			;acbd	15 	. 
	jr nz,$-28		;acbe	20 e2 	  . 
	ret			;acc0	c9 	. 
	dec a			;acc1	3d 	= 
	add a,a			;acc2	87 	. 
	ld b,000h		;acc3	06 00 	. . 
	ld c,a			;acc5	4f 	O 
	ld ix,0baddh		;acc6	dd 21 dd ba 	. ! . . 
	add ix,bc		;acca	dd 09 	. . 
	ld b,(ix+001h)		;accc	dd 46 01 	. F . 
	ld c,(ix+000h)		;accf	dd 4e 00 	. N . 
	push bc			;acd2	c5 	. 
	pop ix		;acd3	dd e1 	. . 
	ld a,002h		;acd5	3e 02 	> . 
	cp (ix+000h)		;acd7	dd be 00 	. . . 
	jr z,$+37		;acda	28 23 	( # 
	ld a,001h		;acdc	3e 01 	> . 
	cp (ix+000h)		;acde	dd be 00 	. . . 
	jr nz,$+21		;ace1	20 13 	  . 
	inc ix		;ace3	dd 23 	. # 
	ld b,(ix+000h)		;ace5	dd 46 00 	. F . 
	inc ix		;ace8	dd 23 	. # 
	ld a,(ix+000h)		;acea	dd 7e 00 	. ~ . 
	ld (hl),b			;aced	70 	p 
	inc hl			;acee	23 	# 
	dec a			;acef	3d 	= 
	jr nz,$-3		;acf0	20 fb 	  . 
	inc ix		;acf2	dd 23 	. # 
	jr $-31		;acf4	18 df 	. . 
	ld b,(ix+000h)		;acf6	dd 46 00 	. F . 
	ld (hl),b			;acf9	70 	p 
	inc hl			;acfa	23 	# 
	inc ix		;acfb	dd 23 	. # 
	jr $-40		;acfd	18 d6 	. . 
	ret			;acff	c9 	. 
	nop			;ad00	00 	. 
	ld b,000h		;ad01	06 00 	. . 
	ld c,a			;ad03	4f 	O 
	ld ix,0c0d6h		;ad04	dd 21 d6 c0 	. ! . . 
	add ix,bc		;ad08	dd 09 	. . 
	and a			;ad0a	a7 	. 
	rl c		;ad0b	cb 11 	. . 
	rl b		;ad0d	cb 10 	. . 
	rl c		;ad0f	cb 11 	. . 
	rl b		;ad11	cb 10 	. . 
	add ix,bc		;ad13	dd 09 	. . 
	ld a,(ix+000h)		;ad15	dd 7e 00 	. ~ . 
	and a			;ad18	a7 	. 
	jr nz,$+25		;ad19	20 17 	  . 
	ld e,(ix+001h)		;ad1b	dd 5e 01 	. ^ . 
	ld d,(ix+002h)		;ad1e	dd 56 02 	. V . 
	ld l,(ix+003h)		;ad21	dd 6e 03 	. n . 
	ld h,(ix+004h)		;ad24	dd 66 04 	. f . 
	ld iy,00004h		;ad27	fd 21 04 00 	. ! . . 
	ld a,001h		;ad2b	3e 01 	> . 
	call 01fbeh		;ad2d	cd be 1f 	. . . 
	jr $+101		;ad30	18 63 	. c 
	ld l,(ix+003h)		;ad32	dd 6e 03 	. n . 
	ld h,(ix+004h)		;ad35	dd 66 04 	. f . 
	ld e,(ix+001h)		;ad38	dd 5e 01 	. ^ . 
	ld d,(ix+002h)		;ad3b	dd 56 02 	. V . 
	push de			;ad3e	d5 	. 
	pop ix		;ad3f	dd e1 	. . 
	ld b,004h		;ad41	06 04 	. . 
	push bc			;ad43	c5 	. 
	push af			;ad44	f5 	. 
	push hl			;ad45	e5 	. 
	push ix		;ad46	dd e5 	. . 
	ld iy,072e7h		;ad48	fd 21 e7 72 	. ! . r 
	cp 001h		;ad4c	fe 01 	. . 
	jr nz,$+7		;ad4e	20 05 	  . 
	call 0ad96h		;ad50	cd 96 ad 	. . . 
	jr $+32		;ad53	18 1e 	. . 
	cp 002h		;ad55	fe 02 	. . 
	jr nz,$+7		;ad57	20 05 	  . 
	call 0adabh		;ad59	cd ab ad 	. . . 
	jr $+23		;ad5c	18 15 	. . 
	cp 003h		;ad5e	fe 03 	. . 
	jr nz,$+7		;ad60	20 05 	  . 
	call 0adcah		;ad62	cd ca ad 	. . . 
	jr $+14		;ad65	18 0c 	. . 
	cp 004h		;ad67	fe 04 	. . 
	jr nz,$+7		;ad69	20 05 	  . 
	call 0ade9h		;ad6b	cd e9 ad 	. . . 
	jr $+5		;ad6e	18 03 	. . 
	call 0ae0ch		;ad70	cd 0c ae 	. . . 
	pop ix		;ad73	dd e1 	. . 
	ld e,(ix+000h)		;ad75	dd 5e 00 	. ^ . 
	ld d,000h		;ad78	16 00 	. . 
	inc ix		;ad7a	dd 23 	. # 
	push ix		;ad7c	dd e5 	. . 
	ld hl,072e7h		;ad7e	21 e7 72 	! . r 
	ld iy,00001h		;ad81	fd 21 01 00 	. ! . . 
	ld a,001h		;ad85	3e 01 	> . 
	call 01fbeh		;ad87	cd be 1f 	. . . 
	pop ix		;ad8a	dd e1 	. . 
	pop hl			;ad8c	e1 	. 
	ld bc,00008h		;ad8d	01 08 00 	. . . 
	add hl,bc			;ad90	09 	. 
	pop af			;ad91	f1 	. 
	pop bc			;ad92	c1 	. 
	djnz $-80		;ad93	10 ae 	. . 
	ret			;ad95	c9 	. 
	ld b,008h		;ad96	06 08 	. . 
	ld d,(hl)			;ad98	56 	V 
	ld c,008h		;ad99	0e 08 	. . 
	srl d		;ad9b	cb 3a 	. : 
	rl e		;ad9d	cb 13 	. . 
	dec c			;ad9f	0d 	. 
	jr nz,$-5		;ada0	20 f9 	  . 
	ld (iy+000h),e		;ada2	fd 73 00 	. s . 
	inc hl			;ada5	23 	# 
	inc iy		;ada6	fd 23 	. # 
	djnz $-16		;ada8	10 ee 	. . 
	ret			;adaa	c9 	. 
	ld c,008h		;adab	0e 08 	. . 
	push hl			;adad	e5 	. 
	ld d,001h		;adae	16 01 	. . 
	pop hl			;adb0	e1 	. 
	push hl			;adb1	e5 	. 
	ld b,008h		;adb2	06 08 	. . 
	ld a,(hl)			;adb4	7e 	~ 
	and d			;adb5	a2 	. 
	jr z,$+3		;adb6	28 01 	( . 
	scf			;adb8	37 	7 
	rl e		;adb9	cb 13 	. . 
	inc hl			;adbb	23 	# 
	djnz $-8		;adbc	10 f6 	. . 
	ld (iy+000h),e		;adbe	fd 73 00 	. s . 
	inc iy		;adc1	fd 23 	. # 
	rlc d		;adc3	cb 02 	. . 
	dec c			;adc5	0d 	. 
	jr nz,$-22		;adc6	20 e8 	  . 
	pop hl			;adc8	e1 	. 
	ret			;adc9	c9 	. 
	ld c,008h		;adca	0e 08 	. . 
	push hl			;adcc	e5 	. 
	ld d,080h		;adcd	16 80 	. . 
	pop hl			;adcf	e1 	. 
	push hl			;add0	e5 	. 
	ld b,008h		;add1	06 08 	. . 
	ld a,(hl)			;add3	7e 	~ 
	and d			;add4	a2 	. 
	jr z,$+3		;add5	28 01 	( . 
	scf			;add7	37 	7 
	rl e		;add8	cb 13 	. . 
	inc hl			;adda	23 	# 
	djnz $-8		;addb	10 f6 	. . 
	ld (iy+000h),e		;addd	fd 73 00 	. s . 
	inc iy		;ade0	fd 23 	. # 
	rrc d		;ade2	cb 0a 	. . 
	dec c			;ade4	0d 	. 
	jr nz,$-22		;ade5	20 e8 	  . 
	pop hl			;ade7	e1 	. 
	ret			;ade8	c9 	. 
	ld bc,00007h		;ade9	01 07 00 	. . . 
	add hl,bc			;adec	09 	. 
	ld c,008h		;aded	0e 08 	. . 
	ld d,001h		;adef	16 01 	. . 
	push hl			;adf1	e5 	. 
	pop hl			;adf2	e1 	. 
	push hl			;adf3	e5 	. 
	ld b,008h		;adf4	06 08 	. . 
	ld a,(hl)			;adf6	7e 	~ 
	and d			;adf7	a2 	. 
	jr z,$+3		;adf8	28 01 	( . 
	scf			;adfa	37 	7 
	rl e		;adfb	cb 13 	. . 
	dec hl			;adfd	2b 	+ 
	djnz $-8		;adfe	10 f6 	. . 
	ld (iy+000h),e		;ae00	fd 73 00 	. s . 
	inc iy		;ae03	fd 23 	. # 
	rlc d		;ae05	cb 02 	. . 
	dec c			;ae07	0d 	. 
	jr nz,$-22		;ae08	20 e8 	  . 
	pop hl			;ae0a	e1 	. 
	ret			;ae0b	c9 	. 
	ld bc,00007h		;ae0c	01 07 00 	. . . 
	add hl,bc			;ae0f	09 	. 
	ld d,080h		;ae10	16 80 	. . 
	push hl			;ae12	e5 	. 
	ld c,008h		;ae13	0e 08 	. . 
	pop hl			;ae15	e1 	. 
	push hl			;ae16	e5 	. 
	ld b,008h		;ae17	06 08 	. . 
	ld a,(hl)			;ae19	7e 	~ 
	and d			;ae1a	a2 	. 
	jr z,$+3		;ae1b	28 01 	( . 
	scf			;ae1d	37 	7 
	rl e		;ae1e	cb 13 	. . 
	dec hl			;ae20	2b 	+ 
	djnz $-8		;ae21	10 f6 	. . 
	ld (iy+000h),e		;ae23	fd 73 00 	. s . 
	inc iy		;ae26	fd 23 	. # 
	rrc d		;ae28	cb 0a 	. . 
	dec c			;ae2a	0d 	. 
	jr nz,$-22		;ae2b	20 e8 	  . 
	pop hl			;ae2d	e1 	. 
	ret			;ae2e	c9 	. 
	dec a			;ae2f	3d 	= 
	add a,a			;ae30	87 	. 
	ld c,a			;ae31	4f 	O 
	ld b,000h		;ae32	06 00 	. . 
	ld hl,0be21h		;ae34	21 21 be 	! ! . 
	add hl,bc			;ae37	09 	. 
	ld e,(hl)			;ae38	5e 	^ 
	inc hl			;ae39	23 	# 
	ld d,(hl)			;ae3a	56 	V 
	ld ix,0be49h		;ae3b	dd 21 49 be 	. ! I . 
	add ix,bc		;ae3f	dd 09 	. . 
	ld l,(ix+000h)		;ae41	dd 6e 00 	. n . 
	ld h,(ix+001h)		;ae44	dd 66 01 	. f . 
	ld a,(hl)			;ae47	7e 	~ 
	cp 0ffh		;ae48	fe ff 	. . 
	jr z,$+61		;ae4a	28 3b 	( ; 
	cp 0feh		;ae4c	fe fe 	. . 
	jr nz,$+12		;ae4e	20 0a 	  . 
	inc hl			;ae50	23 	# 
	ld c,(hl)			;ae51	4e 	N 
	inc hl			;ae52	23 	# 
	ld b,000h		;ae53	06 00 	. . 
	ex de,hl			;ae55	eb 	. 
	add hl,bc			;ae56	09 	. 
	ex de,hl			;ae57	eb 	. 
	jr $-17		;ae58	18 ed 	. . 
	cp 0fdh		;ae5a	fe fd 	. . 
	jr nz,$+26		;ae5c	20 18 	  . 
	inc hl			;ae5e	23 	# 
	ld b,(hl)			;ae5f	46 	F 
	inc hl			;ae60	23 	# 
	push bc			;ae61	c5 	. 
	push hl			;ae62	e5 	. 
	push de			;ae63	d5 	. 
	ld a,002h		;ae64	3e 02 	> . 
	ld iy,00001h		;ae66	fd 21 01 00 	. ! . . 
	call 01fbeh		;ae6a	cd be 1f 	. . . 
	pop de			;ae6d	d1 	. 
	pop hl			;ae6e	e1 	. 
	pop bc			;ae6f	c1 	. 
	inc de			;ae70	13 	. 
	djnz $-16		;ae71	10 ee 	. . 
	inc hl			;ae73	23 	# 
	jr $-45		;ae74	18 d1 	. . 
	push hl			;ae76	e5 	. 
	push de			;ae77	d5 	. 
	ld iy,00001h		;ae78	fd 21 01 00 	. ! . . 
	ld a,002h		;ae7c	3e 02 	> . 
	call 01fbeh		;ae7e	cd be 1f 	. . . 
	pop de			;ae81	d1 	. 
	pop hl			;ae82	e1 	. 
	inc de			;ae83	13 	. 
	inc hl			;ae84	23 	# 
	jr $-62		;ae85	18 c0 	. . 
	ret			;ae87	c9 	. 
	ld ix,0aeadh		;ae88	dd 21 ad ae 	. ! . . 
	ld b,005h		;ae8c	06 05 	. . 
	push bc			;ae8e	c5 	. 
	xor a			;ae8f	af 	. 
	ex de,hl			;ae90	eb 	. 
	ld c,(ix+000h)		;ae91	dd 4e 00 	. N . 
	ld b,(ix+001h)		;ae94	dd 46 01 	. F . 
	and a			;ae97	a7 	. 
	sbc hl,bc		;ae98	ed 42 	. B 
	jr c,$+5		;ae9a	38 03 	8 . 
	inc a			;ae9c	3c 	< 
	jr $-6		;ae9d	18 f8 	. . 
	add hl,bc			;ae9f	09 	. 
	ex de,hl			;aea0	eb 	. 
	add a,0d8h		;aea1	c6 d8 	. . 
	ld (hl),a			;aea3	77 	w 
	inc hl			;aea4	23 	# 
	inc ix		;aea5	dd 23 	. # 
	inc ix		;aea7	dd 23 	. # 
	pop bc			;aea9	c1 	. 
	djnz $-28		;aeaa	10 e2 	. . 
	ret			;aeac	c9 	. 
	djnz $+41		;aead	10 27 	. ' 
	ret pe			;aeaf	e8 	. 
	inc bc			;aeb0	03 	. 
	ld h,h			;aeb1	64 	d 
	nop			;aeb2	00 	. 
	ld a,(bc)			;aeb3	0a 	. 
	nop			;aeb4	00 	. 
	ld bc,04700h		;aeb5	01 00 47 	. . G 
	ld a,(07139h)		;aeb8	3a 39 71 	: 9 q 
	dec a			;aebb	3d 	= 
	jp p,0aec1h		;aebc	f2 c1 ae 	. . . 
	ld a,04fh		;aebf	3e 4f 	> O 
	ld e,a			;aec1	5f 	_ 
	ld d,000h		;aec2	16 00 	. . 
	ld hl,0713ah		;aec4	21 3a 71 	! : q 
	add hl,de			;aec7	19 	. 
	ld a,(hl)			;aec8	7e 	~ 
	cp b			;aec9	b8 	. 
	jr z,$+22		;aeca	28 14 	( . 
	ld a,(07139h)		;aecc	3a 39 71 	: 9 q 
	ld d,000h		;aecf	16 00 	. . 
	ld e,a			;aed1	5f 	_ 
	ld hl,0713ah		;aed2	21 3a 71 	! : q 
	add hl,de			;aed5	19 	. 
	ld (hl),b			;aed6	70 	p 
	inc a			;aed7	3c 	< 
	cp 050h		;aed8	fe 50 	. P 
	jr c,$+3		;aeda	38 01 	8 . 
	xor a			;aedc	af 	. 
	ld (07139h),a		;aedd	32 39 71 	2 9 q 
	ret			;aee0	c9 	. 
	push af			;aee1	f5 	. 
	ld h,000h		;aee2	26 00 	& . 
	ld a,d			;aee4	7a 	z 
	cp 001h		;aee5	fe 01 	. . 
	ld a,c			;aee7	79 	y 
	jr nz,$+9		;aee8	20 07 	  . 
	add a,00ch		;aeea	c6 0c 	. . 
	jp c,0aff5h		;aeec	da f5 af 	. . . 
	jr $+7		;aeef	18 05 	. . 
	sub 00ch		;aef1	d6 0c 	. . 
	jp c,0aff5h		;aef3	da f5 af 	. . . 
	ld c,a			;aef6	4f 	O 
	ld e,005h		;aef7	1e 05 	. . 
	ld ix,0722ch		;aef9	dd 21 2c 72 	. ! , r 
	bit 7,(ix+000h)		;aefd	dd cb 00 7e 	. . . ~ 
	jr z,$+25		;af01	28 17 	( . 
	ld a,(ix+002h)		;af03	dd 7e 02 	. ~ . 
	cp c			;af06	b9 	. 
	jr nz,$+19		;af07	20 11 	  . 
	ld a,(ix+001h)		;af09	dd 7e 01 	. ~ . 
	cp b			;af0c	b8 	. 
	jr z,$+25		;af0d	28 17 	( . 
	sub 010h		;af0f	d6 10 	. . 
	cp b			;af11	b8 	. 
	jr nc,$+8		;af12	30 06 	0 . 
	add a,01fh		;af14	c6 1f 	. . 
	cp b			;af16	b8 	. 
	jp nc,0b061h		;af17	d2 61 b0 	. a . 
	push de			;af1a	d5 	. 
	ld de,00005h		;af1b	11 05 00 	. . . 
	add ix,de		;af1e	dd 19 	. . 
	pop de			;af20	d1 	. 
	dec e			;af21	1d 	. 
	jr nz,$-37		;af22	20 d9 	  . 
	jr $+82		;af24	18 50 	. P 
	ld a,(ix+000h)		;af26	dd 7e 00 	. ~ . 
	and 078h		;af29	e6 78 	. x 
	jp nz,0afd2h		;af2b	c2 d2 af 	. . . 
	inc h			;af2e	24 	$ 
	pop af			;af2f	f1 	. 
	push af			;af30	f5 	. 
	cp 002h		;af31	fe 02 	. . 
	jp z,0aee4h		;af33	ca e4 ae 	. . . 
	cp 003h		;af36	fe 03 	. . 
	jr nz,$-84		;af38	20 aa 	  . 
	push bc			;af3a	c5 	. 
	push de			;af3b	d5 	. 
	push hl			;af3c	e5 	. 
	push ix		;af3d	dd e5 	. . 
	ld a,c			;af3f	79 	y 
	bit 0,d		;af40	cb 42 	. B 
	jr z,$+6		;af42	28 04 	( . 
	add a,006h		;af44	c6 06 	. . 
	jr $+4		;af46	18 02 	. . 
	sub 006h		;af48	d6 06 	. . 
	ld c,a			;af4a	4f 	O 
	call 0ac3fh		;af4b	cd 3f ac 	. ? . 
	ld a,c			;af4e	79 	y 
	and 00fh		;af4f	e6 0f 	. . 
	cp 008h		;af51	fe 08 	. . 
	ld a,(ix+000h)		;af53	dd 7e 00 	. ~ . 
	jr nc,$+10		;af56	30 08 	0 . 
	and 005h		;af58	e6 05 	. . 
	cp 005h		;af5a	fe 05 	. . 
	jr nz,$+18		;af5c	20 10 	  . 
	jr $+8		;af5e	18 06 	. . 
	and 00ah		;af60	e6 0a 	. . 
	cp 00ah		;af62	fe 0a 	. . 
	jr nz,$+10		;af64	20 08 	  . 
	pop ix		;af66	dd e1 	. . 
	pop hl			;af68	e1 	. 
	pop de			;af69	d1 	. 
	pop bc			;af6a	c1 	. 
	jp 0aee4h		;af6b	c3 e4 ae 	. . . 
	pop ix		;af6e	dd e1 	. . 
	pop hl			;af70	e1 	. 
	pop de			;af71	d1 	. 
	pop bc			;af72	c1 	. 
	jp 0b061h		;af73	c3 61 b0 	. a . 
	ld e,000h		;af76	1e 00 	. . 
	ld a,h			;af78	7c 	| 
	and a			;af79	a7 	. 
	jp z,0b063h		;af7a	ca 63 b0 	. c . 
	pop af			;af7d	f1 	. 
	push af			;af7e	f5 	. 
	cp 001h		;af7f	fe 01 	. . 
	jr nz,$+86		;af81	20 54 	  T 
	push de			;af83	d5 	. 
	push hl			;af84	e5 	. 
	ld ix,0728eh		;af85	dd 21 8e 72 	. ! . r 
	ld l,007h		;af89	2e 07 	. . 
	bit 7,(ix+004h)		;af8b	dd cb 04 7e 	. . . ~ 
	jr z,$+48		;af8f	28 2e 	( . 
	bit 6,(ix+004h)		;af91	dd cb 04 76 	. . . v 
	jr nz,$+42		;af95	20 28 	  ( 
	ld a,(07272h)		;af97	3a 72 72 	: r r 
	bit 4,a		;af9a	cb 67 	. g 
	jr nz,$+9		;af9c	20 07 	  . 
	ld a,(ix+000h)		;af9e	dd 7e 00 	. ~ . 
	and 030h		;afa1	e6 30 	. 0 
	jr z,$+28		;afa3	28 1a 	( . 
	ld a,(ix+002h)		;afa5	dd 7e 02 	. ~ . 
	sub 00ch		;afa8	d6 0c 	. . 
	cp b			;afaa	b8 	. 
	jr nc,$+20		;afab	30 12 	0 . 
	add a,018h		;afad	c6 18 	. . 
	cp b			;afaf	b8 	. 
	jr c,$+15		;afb0	38 0d 	8 . 
	ld a,(ix+001h)		;afb2	dd 7e 01 	. ~ . 
	sub 004h		;afb5	d6 04 	. . 
	cp c			;afb7	b9 	. 
	jr nc,$+7		;afb8	30 05 	0 . 
	add a,008h		;afba	c6 08 	. . 
	cp c			;afbc	b9 	. 
	jr nc,$+19		;afbd	30 11 	0 . 
	ld de,00006h		;afbf	11 06 00 	. . . 
	add ix,de		;afc2	dd 19 	. . 
	dec l			;afc4	2d 	- 
	jr nz,$-58		;afc5	20 c4 	  . 
	pop hl			;afc7	e1 	. 
	pop de			;afc8	d1 	. 
	call 0b066h		;afc9	cd 66 b0 	. f . 
	jr nz,$+6		;afcc	20 04 	  . 
	jr $+40		;afce	18 26 	. & 
	pop hl			;afd0	e1 	. 
	pop de			;afd1	d1 	. 
	ld e,003h		;afd2	1e 03 	. . 
	jp 0b063h		;afd4	c3 63 b0 	. c . 
	ld a,(07284h)		;afd7	3a 84 72 	: . r 
	sub 00ch		;afda	d6 0c 	. . 
	cp b			;afdc	b8 	. 
	jr nc,$+25		;afdd	30 17 	0 . 
	add a,018h		;afdf	c6 18 	. . 
	cp b			;afe1	b8 	. 
	jr c,$+20		;afe2	38 12 	8 . 
	ld a,(07285h)		;afe4	3a 85 72 	: . r 
	sub 004h		;afe7	d6 04 	. . 
	cp c			;afe9	b9 	. 
	jr nc,$+12		;afea	30 0a 	0 . 
	add a,008h		;afec	c6 08 	. . 
	cp c			;afee	b9 	. 
	jr c,$+7		;afef	38 05 	8 . 
	ld e,003h		;aff1	1e 03 	. . 
	jr $+112		;aff3	18 6e 	. n 
	ld c,a			;aff5	4f 	O 
	ld e,000h		;aff6	1e 00 	. . 
	ld a,h			;aff8	7c 	| 
	and a			;aff9	a7 	. 
	jr z,$+105		;affa	28 67 	( g 
	ld a,d			;affc	7a 	z 
	cp 001h		;affd	fe 01 	. . 
	ld a,c			;afff	79 	y 
	jr nz,$+6		;b000	20 04 	  . 
	sub 00ch		;b002	d6 0c 	. . 
	jr $+4		;b004	18 02 	. . 
	add a,00ch		;b006	c6 0c 	. . 
	ld c,a			;b008	4f 	O 
	ld ix,0722ch		;b009	dd 21 2c 72 	. ! , r 
	ld e,005h		;b00d	1e 05 	. . 
	bit 7,(ix+000h)		;b00f	dd cb 00 7e 	. . . ~ 
	jr z,$+61		;b013	28 3b 	( ; 
	ld a,(ix+001h)		;b015	dd 7e 01 	. ~ . 
	cp b			;b018	b8 	. 
	jr nz,$+55		;b019	20 35 	  5 
	ld a,(ix+002h)		;b01b	dd 7e 02 	. ~ . 
	cp c			;b01e	b9 	. 
	jr nz,$+49		;b01f	20 2f 	  / 
	ld a,d			;b021	7a 	z 
	cp 001h		;b022	fe 01 	. . 
	ld a,c			;b024	79 	y 
	jr nz,$+10		;b025	20 08 	  . 
	add a,004h		;b027	c6 04 	. . 
	cp 0e9h		;b029	fe e9 	. . 
	jr nc,$+54		;b02b	30 34 	0 4 
	jr $+8		;b02d	18 06 	. . 
	sub 004h		;b02f	d6 04 	. . 
	cp 018h		;b031	fe 18 	. . 
	jr c,$+46		;b033	38 2c 	8 , 
	ld (ix+002h),a		;b035	dd 77 02 	. w . 
	push bc			;b038	c5 	. 
	push de			;b039	d5 	. 
	push hl			;b03a	e5 	. 
	push ix		;b03b	dd e5 	. . 
	ld c,a			;b03d	4f 	O 
	ld b,(ix+001h)		;b03e	dd 46 01 	. F . 
	ld a,011h		;b041	3e 11 	> . 
	sub e			;b043	93 	. 
	ld d,001h		;b044	16 01 	. . 
	call 0b629h		;b046	cd 29 b6 	. ) . 
	pop ix		;b049	dd e1 	. . 
	pop hl			;b04b	e1 	. 
	pop de			;b04c	d1 	. 
	pop bc			;b04d	c1 	. 
	jr $+12		;b04e	18 0a 	. . 
	push de			;b050	d5 	. 
	ld de,00005h		;b051	11 05 00 	. . . 
	add ix,de		;b054	dd 19 	. . 
	pop de			;b056	d1 	. 
	dec e			;b057	1d 	. 
	jr nz,$-73		;b058	20 b5 	  . 
	dec h			;b05a	25 	% 
	jr nz,$-95		;b05b	20 9f 	  . 
	ld e,001h		;b05d	1e 01 	. . 
	jr $+4		;b05f	18 02 	. . 
	ld e,002h		;b061	1e 02 	. . 
	pop af			;b063	f1 	. 
	ld a,e			;b064	7b 	{ 
	ret			;b065	c9 	. 
	push iy		;b066	fd e5 	. . 
	push hl			;b068	e5 	. 
	ld iy,0728eh		;b069	fd 21 8e 72 	. ! . r 
	ld hl,00207h		;b06d	21 07 02 	! . . 
	ld a,(iy+004h)		;b070	fd 7e 04 	. ~ . 
	bit 7,a		;b073	cb 7f 	.  
	jp z,0b105h		;b075	ca 05 b1 	. . . 
	bit 6,a		;b078	cb 77 	. w 
	jp nz,0b105h		;b07a	c2 05 b1 	. . . 
	ld a,(iy+000h)		;b07d	fd 7e 00 	. ~ . 
	and 030h		;b080	e6 30 	. 0 
	jp nz,0b105h		;b082	c2 05 b1 	. . . 
	ld a,(iy+002h)		;b085	fd 7e 02 	. ~ . 
	sub b			;b088	90 	. 
	jr nc,$+4		;b089	30 02 	0 . 
	cpl			;b08b	2f 	/ 
	inc a			;b08c	3c 	< 
	cp 010h		;b08d	fe 10 	. . 
	jr nc,$+118		;b08f	30 74 	0 t 
	ld a,(iy+001h)		;b091	fd 7e 01 	. ~ . 
	bit 0,d		;b094	cb 42 	. B 
	jr nz,$+33		;b096	20 1f 	  . 
	cp c			;b098	b9 	. 
	jr c,$+108		;b099	38 6a 	8 j 
	sub 009h		;b09b	d6 09 	. . 
	cp c			;b09d	b9 	. 
	jr nc,$+103		;b09e	30 65 	0 e 
	push bc			;b0a0	c5 	. 
	push de			;b0a1	d5 	. 
	push hl			;b0a2	e5 	. 
	call 09f29h		;b0a3	cd 29 9f 	. ) . 
	pop hl			;b0a6	e1 	. 
	pop de			;b0a7	d1 	. 
	pop bc			;b0a8	c1 	. 
	bit 7,a		;b0a9	cb 7f 	.  
	jr z,$+45		;b0ab	28 2b 	( + 
	ld a,(iy+001h)		;b0ad	fd 7e 01 	. ~ . 
	sub 004h		;b0b0	d6 04 	. . 
	ld (iy+001h),a		;b0b2	fd 77 01 	. w . 
	jr $-48		;b0b5	18 ce 	. . 
	cp c			;b0b7	b9 	. 
	jr z,$+4		;b0b8	28 02 	( . 
	jr nc,$+75		;b0ba	30 49 	0 I 
	add a,009h		;b0bc	c6 09 	. . 
	cp c			;b0be	b9 	. 
	jr c,$+70		;b0bf	38 44 	8 D 
	push bc			;b0c1	c5 	. 
	push de			;b0c2	d5 	. 
	push hl			;b0c3	e5 	. 
	call 09f29h		;b0c4	cd 29 9f 	. ) . 
	pop hl			;b0c7	e1 	. 
	pop de			;b0c8	d1 	. 
	pop bc			;b0c9	c1 	. 
	bit 6,a		;b0ca	cb 77 	. w 
	jr z,$+12		;b0cc	28 0a 	( . 
	ld a,(iy+001h)		;b0ce	fd 7e 01 	. ~ . 
	add a,004h		;b0d1	c6 04 	. . 
	ld (iy+001h),a		;b0d3	fd 77 01 	. w . 
	jr $-81		;b0d6	18 ad 	. . 
	push af			;b0d8	f5 	. 
	ld a,(iy+002h)		;b0d9	fd 7e 02 	. ~ . 
	cp b			;b0dc	b8 	. 
	jr c,$+27		;b0dd	38 19 	8 . 
	pop af			;b0df	f1 	. 
	bit 5,a		;b0e0	cb 6f 	. o 
	jr z,$+12		;b0e2	28 0a 	( . 
	ld a,(iy+002h)		;b0e4	fd 7e 02 	. ~ . 
	add a,004h		;b0e7	c6 04 	. . 
	ld (iy+002h),a		;b0e9	fd 77 02 	. w . 
	jr $+25		;b0ec	18 17 	. . 
	push af			;b0ee	f5 	. 
	ld a,(iy+002h)		;b0ef	fd 7e 02 	. ~ . 
	cp b			;b0f2	b8 	. 
	jr z,$+5		;b0f3	28 03 	( . 
	pop af			;b0f5	f1 	. 
	jr $+48		;b0f6	18 2e 	. . 
	pop af			;b0f8	f1 	. 
	bit 4,a		;b0f9	cb 67 	. g 
	jr z,$+43		;b0fb	28 29 	( ) 
	ld a,(iy+002h)		;b0fd	fd 7e 02 	. ~ . 
	sub 004h		;b100	d6 04 	. . 
	ld (iy+002h),a		;b102	fd 77 02 	. w . 
	push de			;b105	d5 	. 
	ld de,00006h		;b106	11 06 00 	. . . 
	add iy,de		;b109	fd 19 	. . 
	pop de			;b10b	d1 	. 
	dec l			;b10c	2d 	- 
	jp nz,0b070h		;b10d	c2 70 b0 	. p . 
	dec h			;b110	25 	% 
	jr z,$+18		;b111	28 10 	( . 
	ld a,(072bah)		;b113	3a ba 72 	: . r 
	bit 6,a		;b116	cb 77 	. w 
	jr z,$+11		;b118	28 09 	( . 
	ld iy,072bdh		;b11a	fd 21 bd 72 	. ! . r 
	ld l,001h		;b11e	2e 01 	. . 
	jp 0b085h		;b120	c3 85 b0 	. . . 
	xor a			;b123	af 	. 
	jr $+4		;b124	18 02 	. . 
	ld a,001h		;b126	3e 01 	> . 
	pop hl			;b128	e1 	. 
	pop iy		;b129	fd e1 	. . 
	and a			;b12b	a7 	. 
	ret			;b12c	c9 	. 
	ld ix,0722ch		;b12d	dd 21 2c 72 	. ! , r 
	ld e,005h		;b131	1e 05 	. . 
	bit 7,(ix+000h)		;b133	dd cb 00 7e 	. . . ~ 
	jr z,$+44		;b137	28 2a 	( * 
	ld a,b			;b139	78 	x 
	bit 1,d		;b13a	cb 4a 	. J 
	jr z,$+13		;b13c	28 0b 	( . 
	sub (ix+001h)		;b13e	dd 96 01 	. . . 
	jr c,$+34		;b141	38 20 	8   
	cp 00dh		;b143	fe 0d 	. . 
	jr nc,$+30		;b145	30 1c 	0 . 
	jr $+15		;b147	18 0d 	. . 
	sub (ix+001h)		;b149	dd 96 01 	. . . 
	jr z,$+10		;b14c	28 08 	( . 
	jr nc,$+21		;b14e	30 13 	0 . 
	cpl			;b150	2f 	/ 
	inc a			;b151	3c 	< 
	cp 00dh		;b152	fe 0d 	. . 
	jr nc,$+15		;b154	30 0d 	0 . 
	ld a,(ix+002h)		;b156	dd 7e 02 	. ~ . 
	add a,009h		;b159	c6 09 	. . 
	cp c			;b15b	b9 	. 
	jr c,$+7		;b15c	38 05 	8 . 
	sub 012h		;b15e	d6 12 	. . 
	cp c			;b160	b9 	. 
	jr c,$+15		;b161	38 0d 	8 . 
	ex de,hl			;b163	eb 	. 
	ld de,00005h		;b164	11 05 00 	. . . 
	add ix,de		;b167	dd 19 	. . 
	ex de,hl			;b169	eb 	. 
	dec e			;b16a	1d 	. 
	jr nz,$-56		;b16b	20 c6 	  . 
	xor a			;b16d	af 	. 
	jr $+4		;b16e	18 02 	. . 
	ld a,001h		;b170	3e 01 	> . 
	ret			;b172	c9 	. 
	ld a,d			;b173	7a 	z 
	push af			;b174	f5 	. 
	ld hl,07245h		;b175	21 45 72 	! E r 
	call 0ac0bh		;b178	cd 0b ac 	. . . 
	jr z,$+29		;b17b	28 1b 	( . 
	pop af			;b17d	f1 	. 
	push af			;b17e	f5 	. 
	dec a			;b17f	3d 	= 
	ld c,a			;b180	4f 	O 
	ld b,000h		;b181	06 00 	. . 
	ld hl,0718ah		;b183	21 8a 71 	! . q 
	add hl,bc			;b186	09 	. 
	ld a,(hl)			;b187	7e 	~ 
	and 00fh		;b188	e6 0f 	. . 
	cp 00fh		;b18a	fe 0f 	. . 
	jr nz,$+12		;b18c	20 0a 	  . 
	pop af			;b18e	f1 	. 
	ld hl,07245h		;b18f	21 45 72 	! E r 
	call 0abf6h		;b192	cd f6 ab 	. . . 
	scf			;b195	37 	7 
	jr $+4		;b196	18 02 	. . 
	pop af			;b198	f1 	. 
	and a			;b199	a7 	. 
	ret			;b19a	c9 	. 
	nop			;b19b	00 	. 
	push af			;b19c	f5 	. 
	cp 048h		;b19d	fe 48 	. H 
	jp z,0b24eh		;b19f	ca 4e b2 	. N . 
	dec a			;b1a2	3d 	= 
	ld c,a			;b1a3	4f 	O 
	ld b,000h		;b1a4	06 00 	. . 
	ld iy,0718ah		;b1a6	fd 21 8a 71 	. ! . q 
	add iy,bc		;b1aa	fd 09 	. . 
	pop af			;b1ac	f1 	. 
	push af			;b1ad	f5 	. 
	call 0b591h		;b1ae	cd 91 b5 	. . . 
	ld ix,0b250h		;b1b1	dd 21 50 b2 	. ! P . 
	ld bc,00003h		;b1b5	01 03 00 	. . . 
	ld a,(ix+000h)		;b1b8	dd 7e 00 	. ~ . 
	and (iy+000h)		;b1bb	fd a6 00 	. . . 
	jr nz,$+59		;b1be	20 39 	  9 
	pop af			;b1c0	f1 	. 
	push af			;b1c1	f5 	. 
	push de			;b1c2	d5 	. 
	push ix		;b1c3	dd e5 	. . 
	push bc			;b1c5	c5 	. 
	ld hl,07245h		;b1c6	21 45 72 	! E r 
	call 0ac0bh		;b1c9	cd 0b ac 	. . . 
	pop bc			;b1cc	c1 	. 
	pop ix		;b1cd	dd e1 	. . 
	pop de			;b1cf	d1 	. 
	jr z,$+8		;b1d0	28 06 	( . 
	ld hl,0b278h		;b1d2	21 78 b2 	! x . 
	add hl,bc			;b1d5	09 	. 
	jr $+83		;b1d6	18 51 	. Q 
	push bc			;b1d8	c5 	. 
	ld a,(0726eh)		;b1d9	3a 6e 72 	: n r 
	bit 1,a		;b1dc	cb 4f 	. O 
	ld a,(07274h)		;b1de	3a 74 72 	: t r 
	jr z,$+5		;b1e1	28 03 	( . 
	ld a,(07275h)		;b1e3	3a 75 72 	: u r 
	cp 00bh		;b1e6	fe 0b 	. . 
	jr c,$+6		;b1e8	38 04 	8 . 
	sub 00ah		;b1ea	d6 0a 	. . 
	jr $-6		;b1ec	18 f8 	. . 
	dec a			;b1ee	3d 	= 
	ld c,a			;b1ef	4f 	O 
	ld b,000h		;b1f0	06 00 	. . 
	ld hl,0b27ch		;b1f2	21 7c b2 	! | . 
	add hl,bc			;b1f5	09 	. 
	pop bc			;b1f6	c1 	. 
	jr $+50		;b1f7	18 30 	. 0 
	ld hl,0b268h		;b1f9	21 68 b2 	! h . 
	ld a,(iy+000h)		;b1fc	fd 7e 00 	. ~ . 
	and (ix+001h)		;b1ff	dd a6 01 	. . . 
	jr z,$+8		;b202	28 06 	( . 
	push bc			;b204	c5 	. 
	ld bc,00008h		;b205	01 08 00 	. . . 
	add hl,bc			;b208	09 	. 
	pop bc			;b209	c1 	. 
	ld a,(iy+000h)		;b20a	fd 7e 00 	. ~ . 
	and (ix+002h)		;b20d	dd a6 02 	. . . 
	jr z,$+6		;b210	28 04 	( . 
	inc hl			;b212	23 	# 
	inc hl			;b213	23 	# 
	inc hl			;b214	23 	# 
	inc hl			;b215	23 	# 
	ld a,(iy+000h)		;b216	fd 7e 00 	. ~ . 
	and (ix+003h)		;b219	dd a6 03 	. . . 
	jr z,$+4		;b21c	28 02 	( . 
	inc hl			;b21e	23 	# 
	inc hl			;b21f	23 	# 
	ld a,(iy+000h)		;b220	fd 7e 00 	. ~ . 
	and (ix+004h)		;b223	dd a6 04 	. . . 
	jr z,$+3		;b226	28 01 	( . 
	inc hl			;b228	23 	# 
	push bc			;b229	c5 	. 
	push de			;b22a	d5 	. 
	push ix		;b22b	dd e5 	. . 
	push iy		;b22d	fd e5 	. . 
	ld iy,00001h		;b22f	fd 21 01 00 	. ! . . 
	ld a,002h		;b233	3e 02 	> . 
	call 01fbeh		;b235	cd be 1f 	. . . 
	pop iy		;b238	fd e1 	. . 
	pop ix		;b23a	dd e1 	. . 
	pop de			;b23c	d1 	. 
	ld l,(ix+005h)		;b23d	dd 6e 05 	. n . 
	ld h,000h		;b240	26 00 	& . 
	add hl,de			;b242	19 	. 
	ex de,hl			;b243	eb 	. 
	ld bc,00006h		;b244	01 06 00 	. . . 
	add ix,bc		;b247	dd 09 	. . 
	pop bc			;b249	c1 	. 
	dec c			;b24a	0d 	. 
	jp p,0b1b8h		;b24b	f2 b8 b1 	. . . 
	pop af			;b24e	f1 	. 
	ret			;b24f	c9 	. 
	ld bc,00410h		;b250	01 10 04 	. . . 
	ld (bc),a			;b253	02 	. 
	add a,b			;b254	80 	. 
	ld bc,01002h		;b255	01 02 10 	. . . 
	ex af,af'			;b258	08 	. 
	ld b,b			;b259	40 	@ 
	ld bc,0041fh		;b25a	01 1f 04 	. . . 
	ld bc,00820h		;b25d	01 20 08 	.   . 
	add a,b			;b260	80 	. 
	ld bc,00208h		;b261	01 08 02 	. . . 
	jr nz,$+66		;b264	20 40 	  @ 
	inc b			;b266	04 	. 
	nop			;b267	00 	. 
	nop			;b268	00 	. 
	nop			;b269	00 	. 
	nop			;b26a	00 	. 
	nop			;b26b	00 	. 
	nop			;b26c	00 	. 
	ld e,l			;b26d	5d 	] 
	ld e,h			;b26e	5c 	\ 
	ld e,d			;b26f	5a 	Z 
	nop			;b270	00 	. 
	ld e,a			;b271	5f 	_ 
	ld e,(hl)			;b272	5e 	^ 
	ld e,e			;b273	5b 	[ 
	nop			;b274	00 	. 
	ld e,c			;b275	59 	Y 
	ld e,b			;b276	58 	X 
	nop			;b277	00 	. 
	ld de,00910h		;b278	11 10 09 	. . . 
	ex af,af'			;b27b	08 	. 
	ld d,b			;b27c	50 	P 
	ld d,c			;b27d	51 	Q 
	ld d,d			;b27e	52 	R 
	ld d,b			;b27f	50 	P 
	ld d,e			;b280	53 	S 
	ld d,d			;b281	52 	R 
	ld d,h			;b282	54 	T 
	ld d,b			;b283	50 	P 
	ld d,d			;b284	52 	R 
	ld d,e			;b285	53 	S 
	cp 00bh		;b286	fe 0b 	. . 
	jr c,$+6		;b288	38 04 	8 . 
	sub 00ah		;b28a	d6 0a 	. . 
	jr $-6		;b28c	18 f8 	. . 
	push af			;b28e	f5 	. 
	ld hl,0718ah		;b28f	21 8a 71 	! . q 
	ld (hl),000h		;b292	36 00 	6 . 
	ld de,0718bh		;b294	11 8b 71 	. . q 
	ld bc,0009fh		;b297	01 9f 00 	. . . 
	ldir		;b29a	ed b0 	. . 
	ld hl,0718ah		;b29c	21 8a 71 	! . q 
	call 0acc1h		;b29f	cd c1 ac 	. . . 
	pop af			;b2a2	f1 	. 
	dec a			;b2a3	3d 	= 
	add a,a			;b2a4	87 	. 
	ld c,a			;b2a5	4f 	O 
	ld b,000h		;b2a6	06 00 	. . 
	push bc			;b2a8	c5 	. 
	ld ix,0ba01h		;b2a9	dd 21 01 ba 	. ! . . 
	add ix,bc		;b2ad	dd 09 	. . 
	ld l,(ix+000h)		;b2af	dd 6e 00 	. n . 
	ld h,(ix+001h)		;b2b2	dd 66 01 	. f . 
	ld de,07245h		;b2b5	11 45 72 	. E r 
	ld bc,00014h		;b2b8	01 14 00 	. . . 
	ldir		;b2bb	ed b0 	. . 
	call 01ffdh		;b2bd	cd fd 1f 	. . . 
	ld ix,0b961h		;b2c0	dd 21 61 b9 	. ! a . 
	bit 0,a		;b2c4	cb 47 	. G 
	jr z,$+6		;b2c6	28 04 	( . 
	ld ix,0b9b1h		;b2c8	dd 21 b1 b9 	. ! . . 
	pop bc			;b2cc	c1 	. 
	add ix,bc		;b2cd	dd 09 	. . 
	ld l,(ix+000h)		;b2cf	dd 6e 00 	. n . 
	ld h,(ix+001h)		;b2d2	dd 66 01 	. f . 
	ld b,005h		;b2d5	06 05 	. . 
	ld iy,0722ch		;b2d7	fd 21 2c 72 	. ! , r 
	ld a,(hl)			;b2db	7e 	~ 
	push hl			;b2dc	e5 	. 
	push bc			;b2dd	c5 	. 
	call 0abb7h		;b2de	cd b7 ab 	. . . 
	ld (iy+000h),080h		;b2e1	fd 36 00 80 	. 6 . . 
	ld (iy+001h),b		;b2e5	fd 70 01 	. p . 
	ld (iy+002h),c		;b2e8	fd 71 02 	. q . 
	ld (iy+003h),000h		;b2eb	fd 36 03 00 	. 6 . . 
	ld de,00005h		;b2ef	11 05 00 	. . . 
	add iy,de		;b2f2	fd 19 	. . 
	pop bc			;b2f4	c1 	. 
	pop hl			;b2f5	e1 	. 
	inc hl			;b2f6	23 	# 
	djnz $-28		;b2f7	10 e2 	. . 
	ret			;b2f9	c9 	. 
	push iy		;b2fa	fd e5 	. . 
	push hl			;b2fc	e5 	. 
	call 0ac3fh		;b2fd	cd 3f ac 	. ? . 
	ld d,a			;b300	57 	W 
	ld e,000h		;b301	1e 00 	. . 
	ld a,c			;b303	79 	y 
	and 00fh		;b304	e6 0f 	. . 
	cp 008h		;b306	fe 08 	. . 
	jr nz,$+36		;b308	20 22 	  " 
	ld a,(ix+000h)		;b30a	dd 7e 00 	. ~ . 
	and 00ah		;b30d	e6 0a 	. . 
	cp 00ah		;b30f	fe 0a 	. . 
	jr z,$+12		;b311	28 0a 	( . 
	ld e,001h		;b313	1e 01 	. . 
	set 1,(ix+000h)		;b315	dd cb 00 ce 	. . . . 
	set 3,(ix+000h)		;b319	dd cb 00 de 	. . . . 
	push ix		;b31d	dd e5 	. . 
	push de			;b31f	d5 	. 
	ld a,d			;b320	7a 	z 
	ld hl,07259h		;b321	21 59 72 	! Y r 
	call 0abe1h		;b324	cd e1 ab 	. . . 
	pop de			;b327	d1 	. 
	pop ix		;b328	dd e1 	. . 
	jr $+111		;b32a	18 6d 	. m 
	and a			;b32c	a7 	. 
	jr nz,$+67		;b32d	20 41 	  A 
	ld a,(ix+000h)		;b32f	dd 7e 00 	. ~ . 
	and 085h		;b332	e6 85 	. . 
	cp 085h		;b334	fe 85 	. . 
	jr z,$+12		;b336	28 0a 	( . 
	ld e,001h		;b338	1e 01 	. . 
	ld a,(ix+000h)		;b33a	dd 7e 00 	. ~ . 
	or 085h		;b33d	f6 85 	. . 
	ld (ix+000h),a		;b33f	dd 77 00 	. w . 
	push de			;b342	d5 	. 
	push ix		;b343	dd e5 	. . 
	ld a,d			;b345	7a 	z 
	ld hl,07259h		;b346	21 59 72 	! Y r 
	call 0abe1h		;b349	cd e1 ab 	. . . 
	pop ix		;b34c	dd e1 	. . 
	pop de			;b34e	d1 	. 
	push ix		;b34f	dd e5 	. . 
	push de			;b351	d5 	. 
	dec ix		;b352	dd 2b 	. + 
	dec d			;b354	15 	. 
	bit 6,(ix+000h)		;b355	dd cb 00 76 	. . . v 
	jr nz,$+7		;b359	20 05 	  . 
	pop de			;b35b	d1 	. 
	ld e,001h		;b35c	1e 01 	. . 
	push de			;b35e	d5 	. 
	dec d			;b35f	15 	. 
	set 6,(ix+000h)		;b360	dd cb 00 f6 	. . . . 
	ld a,d			;b364	7a 	z 
	ld hl,07259h		;b365	21 59 72 	! Y r 
	call 0abe1h		;b368	cd e1 ab 	. . . 
	pop de			;b36b	d1 	. 
	pop ix		;b36c	dd e1 	. . 
	jr $+43		;b36e	18 29 	. ) 
	pop iy		;b370	fd e1 	. . 
	push iy		;b372	fd e5 	. . 
	cp 004h		;b374	fe 04 	. . 
	jr z,$+21		;b376	28 13 	( . 
	inc ix		;b378	dd 23 	. # 
	ld c,080h		;b37a	0e 80 	. . 
	ld a,(ix+000h)		;b37c	dd 7e 00 	. ~ . 
	dec ix		;b37f	dd 2b 	. + 
	and 005h		;b381	e6 05 	. . 
	cp 005h		;b383	fe 05 	. . 
	jr z,$+20		;b385	28 12 	( . 
	ld b,d			;b387	42 	B 
	inc b			;b388	04 	. 
	jr $+14		;b389	18 0c 	. . 
	ld c,084h		;b38b	0e 84 	. . 
	ld a,(ix+000h)		;b38d	dd 7e 00 	. ~ . 
	and 00ah		;b390	e6 0a 	. . 
	cp 00ah		;b392	fe 0a 	. . 
	jr z,$+5		;b394	28 03 	( . 
	ld b,d			;b396	42 	B 
	ld e,001h		;b397	1e 01 	. . 
	pop hl			;b399	e1 	. 
	pop iy		;b39a	fd e1 	. . 
	ret			;b39c	c9 	. 
	push iy		;b39d	fd e5 	. . 
	push hl			;b39f	e5 	. 
	call 0ac3fh		;b3a0	cd 3f ac 	. ? . 
	ld d,a			;b3a3	57 	W 
	ld e,000h		;b3a4	1e 00 	. . 
	ld a,c			;b3a6	79 	y 
	and 00fh		;b3a7	e6 0f 	. . 
	jr nz,$+67		;b3a9	20 41 	  A 
	bit 7,(ix+000h)		;b3ab	dd cb 00 7e 	. . . ~ 
	jr nz,$+8		;b3af	20 06 	  . 
	ld e,001h		;b3b1	1e 01 	. . 
	set 7,(ix+000h)		;b3b3	dd cb 00 fe 	. . . . 
	push de			;b3b7	d5 	. 
	push ix		;b3b8	dd e5 	. . 
	ld a,d			;b3ba	7a 	z 
	ld hl,07259h		;b3bb	21 59 72 	! Y r 
	call 0abe1h		;b3be	cd e1 ab 	. . . 
	pop ix		;b3c1	dd e1 	. . 
	pop de			;b3c3	d1 	. 
	push ix		;b3c4	dd e5 	. . 
	push de			;b3c6	d5 	. 
	dec ix		;b3c7	dd 2b 	. + 
	dec d			;b3c9	15 	. 
	ld a,(ix+000h)		;b3ca	dd 7e 00 	. ~ . 
	and 04ah		;b3cd	e6 4a 	. J 
	cp 04ah		;b3cf	fe 4a 	. J 
	jr z,$+15		;b3d1	28 0d 	( . 
	pop de			;b3d3	d1 	. 
	ld e,001h		;b3d4	1e 01 	. . 
	push de			;b3d6	d5 	. 
	dec d			;b3d7	15 	. 
	ld a,(ix+000h)		;b3d8	dd 7e 00 	. ~ . 
	or 04ah		;b3db	f6 4a 	. J 
	ld (ix+000h),a		;b3dd	dd 77 00 	. w . 
	ld a,d			;b3e0	7a 	z 
	ld hl,07259h		;b3e1	21 59 72 	! Y r 
	call 0abe1h		;b3e4	cd e1 ab 	. . . 
	pop de			;b3e7	d1 	. 
	pop ix		;b3e8	dd e1 	. . 
	jr $+81		;b3ea	18 4f 	. O 
	cp 008h		;b3ec	fe 08 	. . 
	jr nz,$+36		;b3ee	20 22 	  " 
	ld a,(ix+000h)		;b3f0	dd 7e 00 	. ~ . 
	and 005h		;b3f3	e6 05 	. . 
	cp 005h		;b3f5	fe 05 	. . 
	jr z,$+12		;b3f7	28 0a 	( . 
	ld e,001h		;b3f9	1e 01 	. . 
	set 0,(ix+000h)		;b3fb	dd cb 00 c6 	. . . . 
	set 2,(ix+000h)		;b3ff	dd cb 00 d6 	. . . . 
	ld a,d			;b403	7a 	z 
	ld hl,07259h		;b404	21 59 72 	! Y r 
	push ix		;b407	dd e5 	. . 
	push de			;b409	d5 	. 
	call 0abe1h		;b40a	cd e1 ab 	. . . 
	pop de			;b40d	d1 	. 
	pop ix		;b40e	dd e1 	. . 
	jr $+43		;b410	18 29 	. ) 
	pop iy		;b412	fd e1 	. . 
	push iy		;b414	fd e5 	. . 
	cp 004h		;b416	fe 04 	. . 
	jr nz,$+16		;b418	20 0e 	  . 
	ld c,085h		;b41a	0e 85 	. . 
	ld a,(ix+000h)		;b41c	dd 7e 00 	. ~ . 
	and 005h		;b41f	e6 05 	. . 
	cp 005h		;b421	fe 05 	. . 
	jr z,$+24		;b423	28 16 	( . 
	ld b,d			;b425	42 	B 
	jr $+19		;b426	18 11 	. . 
	ld c,081h		;b428	0e 81 	. . 
	dec ix		;b42a	dd 2b 	. + 
	ld a,(ix+000h)		;b42c	dd 7e 00 	. ~ . 
	inc ix		;b42f	dd 23 	. # 
	and 00ah		;b431	e6 0a 	. . 
	cp 00ah		;b433	fe 0a 	. . 
	jr z,$+6		;b435	28 04 	( . 
	ld b,d			;b437	42 	B 
	dec b			;b438	05 	. 
	ld e,001h		;b439	1e 01 	. . 
	pop hl			;b43b	e1 	. 
	pop iy		;b43c	fd e1 	. . 
	ret			;b43e	c9 	. 
	push iy		;b43f	fd e5 	. . 
	push hl			;b441	e5 	. 
	call 0ac3fh		;b442	cd 3f ac 	. ? . 
	ld d,a			;b445	57 	W 
	ld e,000h		;b446	1e 00 	. . 
	ld a,b			;b448	78 	x 
	and 00fh		;b449	e6 0f 	. . 
	cp 008h		;b44b	fe 08 	. . 
	jr nz,$+70		;b44d	20 44 	  D 
	bit 4,(ix+000h)		;b44f	dd cb 00 66 	. . . f 
	jr nz,$+8		;b453	20 06 	  . 
	ld e,001h		;b455	1e 01 	. . 
	set 4,(ix+000h)		;b457	dd cb 00 e6 	. . . . 
	push de			;b45b	d5 	. 
	push ix		;b45c	dd e5 	. . 
	ld a,d			;b45e	7a 	z 
	ld hl,07259h		;b45f	21 59 72 	! Y r 
	call 0abe1h		;b462	cd e1 ab 	. . . 
	pop ix		;b465	dd e1 	. . 
	pop de			;b467	d1 	. 
	push ix		;b468	dd e5 	. . 
	push de			;b46a	d5 	. 
	ld bc,0fff0h		;b46b	01 f0 ff 	. . . 
	add ix,bc		;b46e	dd 09 	. . 
	ld a,(ix+000h)		;b470	dd 7e 00 	. ~ . 
	and 02ch		;b473	e6 2c 	. , 
	cp 02ch		;b475	fe 2c 	. , 
	jr z,$+14		;b477	28 0c 	( . 
	pop de			;b479	d1 	. 
	ld e,001h		;b47a	1e 01 	. . 
	push de			;b47c	d5 	. 
	ld a,(ix+000h)		;b47d	dd 7e 00 	. ~ . 
	or 02ch		;b480	f6 2c 	. , 
	ld (ix+000h),a		;b482	dd 77 00 	. w . 
	ld a,d			;b485	7a 	z 
	sub 010h		;b486	d6 10 	. . 
	ld hl,07259h		;b488	21 59 72 	! Y r 
	call 0abe1h		;b48b	cd e1 ab 	. . . 
	pop de			;b48e	d1 	. 
	pop ix		;b48f	dd e1 	. . 
	jr $+84		;b491	18 52 	. R 
	and a			;b493	a7 	. 
	jr nz,$+36		;b494	20 22 	  " 
	ld a,(ix+000h)		;b496	dd 7e 00 	. ~ . 
	and 003h		;b499	e6 03 	. . 
	cp 003h		;b49b	fe 03 	. . 
	jr z,$+12		;b49d	28 0a 	( . 
	ld e,001h		;b49f	1e 01 	. . 
	set 0,(ix+000h)		;b4a1	dd cb 00 c6 	. . . . 
	set 1,(ix+000h)		;b4a5	dd cb 00 ce 	. . . . 
	push ix		;b4a9	dd e5 	. . 
	push de			;b4ab	d5 	. 
	ld a,d			;b4ac	7a 	z 
	ld hl,07259h		;b4ad	21 59 72 	! Y r 
	call 0abe1h		;b4b0	cd e1 ab 	. . . 
	pop de			;b4b3	d1 	. 
	pop ix		;b4b4	dd e1 	. . 
	jr $+47		;b4b6	18 2d 	. - 
	cp 004h		;b4b8	fe 04 	. . 
	jr nz,$+16		;b4ba	20 0e 	  . 
	ld a,(ix+000h)		;b4bc	dd 7e 00 	. ~ . 
	and 003h		;b4bf	e6 03 	. . 
	cp 003h		;b4c1	fe 03 	. . 
	jr z,$+34		;b4c3	28 20 	(   
	ld b,d			;b4c5	42 	B 
	ld c,082h		;b4c6	0e 82 	. . 
	jr $+27		;b4c8	18 19 	. . 
	ld bc,0fff0h		;b4ca	01 f0 ff 	. . . 
	add ix,bc		;b4cd	dd 09 	. . 
	ld a,(ix+000h)		;b4cf	dd 7e 00 	. ~ . 
	ld bc,00010h		;b4d2	01 10 00 	. . . 
	add ix,bc		;b4d5	dd 09 	. . 
	and 00ch		;b4d7	e6 0c 	. . 
	cp 00ch		;b4d9	fe 0c 	. . 
	jr z,$+10		;b4db	28 08 	( . 
	ld a,d			;b4dd	7a 	z 
	sub 010h		;b4de	d6 10 	. . 
	ld b,a			;b4e0	47 	G 
	ld c,086h		;b4e1	0e 86 	. . 
	ld e,001h		;b4e3	1e 01 	. . 
	pop hl			;b4e5	e1 	. 
	pop iy		;b4e6	fd e1 	. . 
	ret			;b4e8	c9 	. 
	push iy		;b4e9	fd e5 	. . 
	push hl			;b4eb	e5 	. 
	call 0ac3fh		;b4ec	cd 3f ac 	. ? . 
	ld d,a			;b4ef	57 	W 
	ld a,b			;b4f0	78 	x 
	and 00fh		;b4f1	e6 0f 	. . 
	cp 008h		;b4f3	fe 08 	. . 
	jr nz,$+70		;b4f5	20 44 	  D 
	ld a,(ix+000h)		;b4f7	dd 7e 00 	. ~ . 
	and 013h		;b4fa	e6 13 	. . 
	cp 013h		;b4fc	fe 13 	. . 
	jr z,$+12		;b4fe	28 0a 	( . 
	ld e,001h		;b500	1e 01 	. . 
	ld a,(ix+000h)		;b502	dd 7e 00 	. ~ . 
	or 013h		;b505	f6 13 	. . 
	ld (ix+000h),a		;b507	dd 77 00 	. w . 
	push de			;b50a	d5 	. 
	push ix		;b50b	dd e5 	. . 
	ld a,d			;b50d	7a 	z 
	ld hl,07259h		;b50e	21 59 72 	! Y r 
	call 0abe1h		;b511	cd e1 ab 	. . . 
	pop ix		;b514	dd e1 	. . 
	pop de			;b516	d1 	. 
	push ix		;b517	dd e5 	. . 
	push de			;b519	d5 	. 
	ld bc,0fff0h		;b51a	01 f0 ff 	. . . 
	add ix,bc		;b51d	dd 09 	. . 
	bit 5,(ix+000h)		;b51f	dd cb 00 6e 	. . . n 
	jr nz,$+10		;b523	20 08 	  . 
	pop de			;b525	d1 	. 
	ld e,001h		;b526	1e 01 	. . 
	push de			;b528	d5 	. 
	set 5,(ix+000h)		;b529	dd cb 00 ee 	. . . . 
	ld a,d			;b52d	7a 	z 
	sub 010h		;b52e	d6 10 	. . 
	ld hl,07259h		;b530	21 59 72 	! Y r 
	call 0abe1h		;b533	cd e1 ab 	. . . 
	pop de			;b536	d1 	. 
	pop ix		;b537	dd e1 	. . 
	jr $+84		;b539	18 52 	. R 
	and a			;b53b	a7 	. 
	jr nz,$+36		;b53c	20 22 	  " 
	ld a,(ix+000h)		;b53e	dd 7e 00 	. ~ . 
	and 00ch		;b541	e6 0c 	. . 
	cp 00ch		;b543	fe 0c 	. . 
	jr z,$+12		;b545	28 0a 	( . 
	ld e,001h		;b547	1e 01 	. . 
	set 2,(ix+000h)		;b549	dd cb 00 d6 	. . . . 
	set 3,(ix+000h)		;b54d	dd cb 00 de 	. . . . 
	push ix		;b551	dd e5 	. . 
	push de			;b553	d5 	. 
	ld a,d			;b554	7a 	z 
	ld hl,07259h		;b555	21 59 72 	! Y r 
	call 0abe1h		;b558	cd e1 ab 	. . . 
	pop de			;b55b	d1 	. 
	pop ix		;b55c	dd e1 	. . 
	jr $+47		;b55e	18 2d 	. - 
	cp 004h		;b560	fe 04 	. . 
	jr nz,$+29		;b562	20 1b 	  . 
	ld bc,00010h		;b564	01 10 00 	. . . 
	add ix,bc		;b567	dd 09 	. . 
	ld a,(ix+000h)		;b569	dd 7e 00 	. ~ . 
	ld bc,0fff0h		;b56c	01 f0 ff 	. . . 
	add ix,bc		;b56f	dd 09 	. . 
	and 00ch		;b571	e6 0c 	. . 
	cp 00ch		;b573	fe 0c 	. . 
	jr z,$+24		;b575	28 16 	( . 
	ld a,d			;b577	7a 	z 
	add a,010h		;b578	c6 10 	. . 
	ld b,a			;b57a	47 	G 
	ld c,087h		;b57b	0e 87 	. . 
	jr $+14		;b57d	18 0c 	. . 
	ld a,(ix+000h)		;b57f	dd 7e 00 	. ~ . 
	and 003h		;b582	e6 03 	. . 
	cp 003h		;b584	fe 03 	. . 
	jr z,$+7		;b586	28 05 	( . 
	ld b,d			;b588	42 	B 
	ld c,083h		;b589	0e 83 	. . 
	ld e,001h		;b58b	1e 01 	. . 
	pop hl			;b58d	e1 	. 
	pop iy		;b58e	fd e1 	. . 
	ret			;b590	c9 	. 
	ld hl,00060h		;b591	21 60 00 	! ` . 
	ld de,00040h		;b594	11 40 00 	. @ . 
	dec a			;b597	3d 	= 
	cp 010h		;b598	fe 10 	. . 
	jr c,$+7		;b59a	38 05 	8 . 
	add hl,de			;b59c	19 	. 
	sub 010h		;b59d	d6 10 	. . 
	jr $-7		;b59f	18 f7 	. . 
	add a,a			;b5a1	87 	. 
	ld e,a			;b5a2	5f 	_ 
	add hl,de			;b5a3	19 	. 
	ex de,hl			;b5a4	eb 	. 
	ret			;b5a5	c9 	. 
	add a,a			;b5a6	87 	. 
	add a,a			;b5a7	87 	. 
	ld c,a			;b5a8	4f 	O 
	ld b,000h		;b5a9	06 00 	. . 
	ld hl,0b5d4h		;b5ab	21 d4 b5 	! . . 
	add hl,bc			;b5ae	09 	. 
	ld e,(hl)			;b5af	5e 	^ 
	inc hl			;b5b0	23 	# 
	ld d,(hl)			;b5b1	56 	V 
	inc hl			;b5b2	23 	# 
	push hl			;b5b3	e5 	. 
	ex de,hl			;b5b4	eb 	. 
	ld e,(hl)			;b5b5	5e 	^ 
	inc hl			;b5b6	23 	# 
	ld d,(hl)			;b5b7	56 	V 
	ld hl,072e7h		;b5b8	21 e7 72 	! . r 
	call 0ae88h		;b5bb	cd 88 ae 	. . . 
	ld a,0d8h		;b5be	3e d8 	> . 
	ld (072ech),a		;b5c0	32 ec 72 	2 . r 
	ld a,002h		;b5c3	3e 02 	> . 
	pop hl			;b5c5	e1 	. 
	ld e,(hl)			;b5c6	5e 	^ 
	inc hl			;b5c7	23 	# 
	ld d,(hl)			;b5c8	56 	V 
	ld hl,072e7h		;b5c9	21 e7 72 	! . r 
	ld iy,00006h		;b5cc	fd 21 06 00 	. ! . . 
	call 01fbeh		;b5d0	cd be 1f 	. . . 
	ret			;b5d3	c9 	. 
	ld a,l			;b5d4	7d 	} 
	ld (hl),d			;b5d5	72 	r 
	inc h			;b5d6	24 	$ 
	nop			;b5d7	00 	. 
	ld a,a			;b5d8	7f 	 
	ld (hl),d			;b5d9	72 	r 
	ld b,h			;b5da	44 	D 
	nop			;b5db	00 	. 
	nop			;b5dc	00 	. 
	ld a,b			;b5dd	78 	x 
	sub 007h		;b5de	d6 07 	. . 
	cp (iy+001h)		;b5e0	fd be 01 	. . . 
	jr nc,$+28		;b5e3	30 1a 	0 . 
	add a,00eh		;b5e5	c6 0e 	. . 
	cp (iy+001h)		;b5e7	fd be 01 	. . . 
	jr c,$+21		;b5ea	38 13 	8 . 
	ld a,c			;b5ec	79 	y 
	sub 007h		;b5ed	d6 07 	. . 
	cp (iy+002h)		;b5ef	fd be 02 	. . . 
	jr nc,$+13		;b5f2	30 0b 	0 . 
	add a,00eh		;b5f4	c6 0e 	. . 
	cp (iy+002h)		;b5f6	fd be 02 	. . . 
	jr c,$+6		;b5f9	38 04 	8 . 
	ld a,001h		;b5fb	3e 01 	> . 
	jr $+3		;b5fd	18 01 	. . 
	xor a			;b5ff	af 	. 
	ret			;b600	c9 	. 
	ld ix,0727dh		;b601	dd 21 7d 72 	. ! } r 
	ld c,080h		;b605	0e 80 	. . 
	ld a,(0726eh)		;b607	3a 6e 72 	: n r 
	bit 1,a		;b60a	cb 4f 	. O 
	jr z,$+8		;b60c	28 06 	( . 
	ld ix,0727fh		;b60e	dd 21 7f 72 	. !  r 
	ld c,040h		;b612	0e 40 	. @ 
	ld l,(ix+000h)		;b614	dd 6e 00 	. n . 
	ld h,(ix+001h)		;b617	dd 66 01 	. f . 
	add hl,de			;b61a	19 	. 
	ld (ix+000h),l		;b61b	dd 75 00 	. u . 
	ld (ix+001h),h		;b61e	dd 74 01 	. t . 
	ld a,(0727ch)		;b621	3a 7c 72 	: | r 
	or c			;b624	b1 	. 
	ld (0727ch),a		;b625	32 7c 72 	2 | r 
	ret			;b628	c9 	. 
	ld ix,072dfh		;b629	dd 21 df 72 	. ! . r 
	bit 7,a		;b62d	cb 7f 	.  
	jr z,$+8		;b62f	28 06 	( . 
	ld ix,072e7h		;b631	dd 21 e7 72 	. ! . r 
	and 07fh		;b635	e6 7f 	.  
	push af			;b637	f5 	. 
	push de			;b638	d5 	. 
	add a,a			;b639	87 	. 
	ld e,a			;b63a	5f 	_ 
	ld d,000h		;b63b	16 00 	. . 
	ld hl,0b691h		;b63d	21 91 b6 	! . . 
	add hl,de			;b640	19 	. 
	ld e,(hl)			;b641	5e 	^ 
	inc hl			;b642	23 	# 
	ld d,(hl)			;b643	56 	V 
	ex de,hl			;b644	eb 	. 
	pop de			;b645	d1 	. 
	ld a,d			;b646	7a 	z 
	add a,a			;b647	87 	. 
	ld e,a			;b648	5f 	_ 
	ld d,000h		;b649	16 00 	. . 
	add hl,de			;b64b	19 	. 
	ld a,b			;b64c	78 	x 
	sub 008h		;b64d	d6 08 	. . 
	jr nc,$+6		;b64f	30 04 	0 . 
	ld e,001h		;b651	1e 01 	. . 
	add a,008h		;b653	c6 08 	. . 
	ld (ix+000h),a		;b655	dd 77 00 	. w . 
	ld a,c			;b658	79 	y 
	sub 008h		;b659	d6 08 	. . 
	ld (ix+001h),a		;b65b	dd 77 01 	. w . 
	ld a,(hl)			;b65e	7e 	~ 
	ld (ix+002h),a		;b65f	dd 77 02 	. w . 
	inc hl			;b662	23 	# 
	ld a,(hl)			;b663	7e 	~ 
	bit 0,e		;b664	cb 43 	. C 
	jr z,$+4		;b666	28 02 	( . 
	set 7,a		;b668	cb ff 	. . 
	ld (ix+003h),a		;b66a	dd 77 03 	. w . 
	ld a,(0726eh)		;b66d	3a 6e 72 	: n r 
	set 3,a		;b670	cb df 	. . 
	ld (0726eh),a		;b672	32 6e 72 	2 n r 
	pop af			;b675	f1 	. 
	add a,a			;b676	87 	. 
	add a,a			;b677	87 	. 
	ld e,a			;b678	5f 	_ 
	ld d,000h		;b679	16 00 	. . 
	ld hl,070e9h		;b67b	21 e9 70 	! . p 
	add hl,de			;b67e	19 	. 
	ex de,hl			;b67f	eb 	. 
	push ix		;b680	dd e5 	. . 
	pop hl			;b682	e1 	. 
	ld bc,00004h		;b683	01 04 00 	. . . 
	ldir		;b686	ed b0 	. . 
	ld a,(0726eh)		;b688	3a 6e 72 	: n r 
	res 3,a		;b68b	cb 9f 	. . 
	ld (0726eh),a		;b68d	32 6e 72 	2 n r 
	ret			;b690	c9 	. 
	jp 0c7b6h		;b691	c3 b6 c7 	. . . 
	or (hl)			;b694	b6 	. 
	res 6,(hl)		;b695	cb b6 	. . 
	rst 8			;b697	cf 	. 
	or (hl)			;b698	b6 	. 
	ei			;b699	fb 	. 
	or (hl)			;b69a	b6 	. 
	dec bc			;b69b	0b 	. 
	or a			;b69c	b7 	. 
	dec bc			;b69d	0b 	. 
	or a			;b69e	b7 	. 
	dec bc			;b69f	0b 	. 
	or a			;b6a0	b7 	. 
	dec bc			;b6a1	0b 	. 
	or a			;b6a2	b7 	. 
	dec bc			;b6a3	0b 	. 
	or a			;b6a4	b7 	. 
	dec bc			;b6a5	0b 	. 
	or a			;b6a6	b7 	. 
	dec bc			;b6a7	0b 	. 
	or a			;b6a8	b7 	. 
	ld d,a			;b6a9	57 	W 
	or a			;b6aa	b7 	. 
	ld d,a			;b6ab	57 	W 
	or a			;b6ac	b7 	. 
	ld d,a			;b6ad	57 	W 
	or a			;b6ae	b7 	. 
	ld d,a			;b6af	57 	W 
	or a			;b6b0	b7 	. 
	ld d,a			;b6b1	57 	W 
	or a			;b6b2	b7 	. 
	ld h,c			;b6b3	61 	a 
	or a			;b6b4	b7 	. 
	ld h,c			;b6b5	61 	a 
	or a			;b6b6	b7 	. 
	ld h,c			;b6b7	61 	a 
	or a			;b6b8	b7 	. 
	nop			;b6b9	00 	. 
	nop			;b6ba	00 	. 
	nop			;b6bb	00 	. 
	nop			;b6bc	00 	. 
	nop			;b6bd	00 	. 
	nop			;b6be	00 	. 
	nop			;b6bf	00 	. 
	nop			;b6c0	00 	. 
	nop			;b6c1	00 	. 
	nop			;b6c2	00 	. 
	nop			;b6c3	00 	. 
	nop			;b6c4	00 	. 
	cp b			;b6c5	b8 	. 
	ld a,(bc)			;b6c6	0a 	. 
	or b			;b6c7	b0 	. 
	rrca			;b6c8	0f 	. 
	sub h			;b6c9	94 	. 
	rrca			;b6ca	0f 	. 
	or h			;b6cb	b4 	. 
	inc bc			;b6cc	03 	. 
	and b			;b6cd	a0 	. 
	inc bc			;b6ce	03 	. 
	nop			;b6cf	00 	. 
	nop			;b6d0	00 	. 
	ld h,b			;b6d1	60 	` 
	dec bc			;b6d2	0b 	. 
	ld h,h			;b6d3	64 	d 
	dec bc			;b6d4	0b 	. 
	ld l,b			;b6d5	68 	h 
	dec bc			;b6d6	0b 	. 
	ld l,h			;b6d7	6c 	l 
	dec bc			;b6d8	0b 	. 
	ld (hl),b			;b6d9	70 	p 
	dec bc			;b6da	0b 	. 
	ld (hl),h			;b6db	74 	t 
	dec bc			;b6dc	0b 	. 
	ld a,b			;b6dd	78 	x 
	dec bc			;b6de	0b 	. 
	ld a,h			;b6df	7c 	| 
	dec bc			;b6e0	0b 	. 
	add a,b			;b6e1	80 	. 
	dec bc			;b6e2	0b 	. 
	add a,h			;b6e3	84 	. 
	dec bc			;b6e4	0b 	. 
	sub h			;b6e5	94 	. 
	dec bc			;b6e6	0b 	. 
	ld h,b			;b6e7	60 	` 
	ex af,af'			;b6e8	08 	. 
	ld h,h			;b6e9	64 	d 
	ex af,af'			;b6ea	08 	. 
	ld l,b			;b6eb	68 	h 
	ex af,af'			;b6ec	08 	. 
	ld l,h			;b6ed	6c 	l 
	ex af,af'			;b6ee	08 	. 
	ld (hl),b			;b6ef	70 	p 
	ex af,af'			;b6f0	08 	. 
	ld (hl),h			;b6f1	74 	t 
	ex af,af'			;b6f2	08 	. 
	ld a,b			;b6f3	78 	x 
	ex af,af'			;b6f4	08 	. 
	ld a,h			;b6f5	7c 	| 
	ex af,af'			;b6f6	08 	. 
	add a,b			;b6f7	80 	. 
	ex af,af'			;b6f8	08 	. 
	add a,h			;b6f9	84 	. 
	ex af,af'			;b6fa	08 	. 
	nop			;b6fb	00 	. 
	nop			;b6fc	00 	. 
	sbc a,h			;b6fd	9c 	. 
	ld a,(bc)			;b6fe	0a 	. 
	ret nz			;b6ff	c0 	. 
	ld a,(bc)			;b700	0a 	. 
	call nz,0c80ah		;b701	c4 0a c8 	. . . 
	ld a,(bc)			;b704	0a 	. 
	call z,0d00ah		;b705	cc 0a d0 	. . . 
	ld a,(bc)			;b708	0a 	. 
	call nc,0000ah		;b709	d4 0a 00 	. . . 
	nop			;b70c	00 	. 
	nop			;b70d	00 	. 
	dec c			;b70e	0d 	. 
	inc b			;b70f	04 	. 
	dec c			;b710	0d 	. 
	ex af,af'			;b711	08 	. 
	dec c			;b712	0d 	. 
	inc c			;b713	0c 	. 
	dec c			;b714	0d 	. 
	djnz $+15		;b715	10 0d 	. . 
	inc d			;b717	14 	. 
	dec c			;b718	0d 	. 
	jr $+15		;b719	18 0d 	. . 
	inc e			;b71b	1c 	. 
	dec c			;b71c	0d 	. 
	jr nz,$+15		;b71d	20 0d 	  . 
	inc h			;b71f	24 	$ 
	dec c			;b720	0d 	. 
	jr z,$+15		;b721	28 0d 	( . 
	inc l			;b723	2c 	, 
	dec c			;b724	0d 	. 
	nop			;b725	00 	. 
	rlca			;b726	07 	. 
	inc b			;b727	04 	. 
	rlca			;b728	07 	. 
	ex af,af'			;b729	08 	. 
	rlca			;b72a	07 	. 
	inc c			;b72b	0c 	. 
	rlca			;b72c	07 	. 
	djnz $+9		;b72d	10 07 	. . 
	inc d			;b72f	14 	. 
	rlca			;b730	07 	. 
	jr $+9		;b731	18 07 	. . 
	inc e			;b733	1c 	. 
	rlca			;b734	07 	. 
	jr nz,$+9		;b735	20 07 	  . 
	inc h			;b737	24 	$ 
	rlca			;b738	07 	. 
	jr z,$+9		;b739	28 07 	( . 
	inc l			;b73b	2c 	, 
	rlca			;b73c	07 	. 
	jr nc,$+17		;b73d	30 0f 	0 . 
	inc (hl)			;b73f	34 	4 
	rrca			;b740	0f 	. 
	jr c,$+17		;b741	38 0f 	8 . 
	inc a			;b743	3c 	< 
	rrca			;b744	0f 	. 
	ld b,b			;b745	40 	@ 
	rrca			;b746	0f 	. 
	ld b,h			;b747	44 	D 
	rrca			;b748	0f 	. 
	ld c,b			;b749	48 	H 
	rrca			;b74a	0f 	. 
	ld c,h			;b74b	4c 	L 
	rrca			;b74c	0f 	. 
	ld d,b			;b74d	50 	P 
	rrca			;b74e	0f 	. 
	ld d,h			;b74f	54 	T 
	rrca			;b750	0f 	. 
	ld e,b			;b751	58 	X 
	rrca			;b752	0f 	. 
	ld e,h			;b753	5c 	\ 
	rrca			;b754	0f 	. 
	sub h			;b755	94 	. 
	dec c			;b756	0d 	. 
	nop			;b757	00 	. 
	nop			;b758	00 	. 
	adc a,b			;b759	88 	. 
	ex af,af'			;b75a	08 	. 
	adc a,h			;b75b	8c 	. 
	ex af,af'			;b75c	08 	. 
	sub b			;b75d	90 	. 
	ex af,af'			;b75e	08 	. 
	sbc a,b			;b75f	98 	. 
	rrca			;b760	0f 	. 
	nop			;b761	00 	. 
	nop			;b762	00 	. 
	ret po			;b763	e0 	. 
	dec b			;b764	05 	. 
	call po,0e805h		;b765	e4 05 e8 	. . . 
	dec b			;b768	05 	. 
	call pe,09405h		;b769	ec 05 94 	. . . 
	dec b			;b76c	05 	. 
	ld a,040h		;b76d	3e 40 	> @ 
	ld (072bdh),a		;b76f	32 bd 72 	2 . r 
	ld hl,072c4h		;b772	21 c4 72 	! . r 
	bit 0,(hl)		;b775	cb 46 	. F 
	jr z,$+10		;b777	28 08 	( . 
	res 0,(hl)		;b779	cb 86 	. . 
	ld a,(0727dh)		;b77b	3a 7d 72 	: } r 
	call 01fcah		;b77e	cd ca 1f 	. . . 
	call 0ca24h		;b781	cd 24 ca 	. $ . 
	ld a,001h		;b784	3e 01 	> . 
	ld (072c2h),a		;b786	32 c2 72 	2 . r 
	ld a,(072bah)		;b789	3a ba 72 	: . r 
	res 6,a		;b78c	cb b7 	. . 
	res 5,a		;b78e	cb af 	. . 
	ld (072bah),a		;b790	32 ba 72 	2 . r 
	and 007h		;b793	e6 07 	. . 
	ld c,a			;b795	4f 	O 
	ld b,000h		;b796	06 00 	. . 
	ld hl,0b7bch		;b798	21 bc b7 	! . . 
	add hl,bc			;b79b	09 	. 
	ld b,(hl)			;b79c	46 	F 
	ld hl,072b8h		;b79d	21 b8 72 	! . r 
	ld a,(0726eh)		;b7a0	3a 6e 72 	: n r 
	and 003h		;b7a3	e6 03 	. . 
	cp 003h		;b7a5	fe 03 	. . 
	jr nz,$+3		;b7a7	20 01 	  . 
	inc hl			;b7a9	23 	# 
	ld c,000h		;b7aa	0e 00 	. . 
	ld a,(hl)			;b7ac	7e 	~ 
	or b			;b7ad	b0 	. 
	ld (hl),a			;b7ae	77 	w 
	cp 01fh		;b7af	fe 1f 	. . 
	jr nz,$+3		;b7b1	20 01 	  . 
	inc c			;b7b3	0c 	. 
	ld a,c			;b7b4	79 	y 
	push af			;b7b5	f5 	. 
	call 0b809h		;b7b6	cd 09 b8 	. . . 
	pop af			;b7b9	f1 	. 
	and a			;b7ba	a7 	. 
	ret			;b7bb	c9 	. 
	ld bc,00402h		;b7bc	01 02 04 	. . . 
	ex af,af'			;b7bf	08 	. 
	djnz $+10		;b7c0	10 08 	. . 
	inc b			;b7c2	04 	. 
	ld (bc),a			;b7c3	02 	. 
	push hl			;b7c4	e5 	. 
	push ix		;b7c5	dd e5 	. . 
	ld a,0c0h		;b7c7	3e c0 	> . 
	ld (ix+004h),a		;b7c9	dd 77 04 	. w . 
	ld a,008h		;b7cc	3e 08 	> . 
	ld b,a			;b7ce	47 	G 
	ld c,a			;b7cf	4f 	O 
	call 0b7efh		;b7d0	cd ef b7 	. . . 
	add a,005h		;b7d3	c6 05 	. . 
	ld d,000h		;b7d5	16 00 	. . 
	call 0b629h		;b7d7	cd 29 b6 	. ) . 
	ld hl,07278h		;b7da	21 78 72 	! x r 
	ld a,(0726eh)		;b7dd	3a 6e 72 	: n r 
	and 003h		;b7e0	e6 03 	. . 
	cp 003h		;b7e2	fe 03 	. . 
	jr nz,$+3		;b7e4	20 01 	  . 
	inc hl			;b7e6	23 	# 
	ld a,(hl)			;b7e7	7e 	~ 
	dec a			;b7e8	3d 	= 
	ld (hl),a			;b7e9	77 	w 
	pop ix		;b7ea	dd e1 	. . 
	pop hl			;b7ec	e1 	. 
	and a			;b7ed	a7 	. 
	ret			;b7ee	c9 	. 
	push de			;b7ef	d5 	. 
	push hl			;b7f0	e5 	. 
	push ix		;b7f1	dd e5 	. . 
	pop hl			;b7f3	e1 	. 
	ld de,0728eh		;b7f4	11 8e 72 	. . r 
	and a			;b7f7	a7 	. 
	sbc hl,de		;b7f8	ed 52 	. R 
	ld a,l			;b7fa	7d 	} 
	ld h,000h		;b7fb	26 00 	& . 
	and a			;b7fd	a7 	. 
	jr z,$+7		;b7fe	28 05 	( . 
	inc h			;b800	24 	$ 
	sub 006h		;b801	d6 06 	. . 
	jr nz,$-3		;b803	20 fb 	  . 
	ld a,h			;b805	7c 	| 
	pop hl			;b806	e1 	. 
	pop de			;b807	d1 	. 
	ret			;b808	c9 	. 
	ld ix,072c7h		;b809	dd 21 c7 72 	. ! . r 
	ld b,003h		;b80d	06 03 	. . 
	bit 7,(ix+004h)		;b80f	dd cb 04 7e 	. . . ~ 
	jr z,$+23		;b813	28 15 	( . 
	bit 7,(ix+000h)		;b815	dd cb 00 7e 	. . . ~ 
	jr nz,$+17		;b819	20 0f 	  . 
	push bc			;b81b	c5 	. 
	call 0b832h		;b81c	cd 32 b8 	. 2 . 
	push ix		;b81f	dd e5 	. . 
	ld de,00032h		;b821	11 32 00 	. 2 . 
	call 0b601h		;b824	cd 01 b6 	. . . 
	pop ix		;b827	dd e1 	. . 
	pop bc			;b829	c1 	. 
	ld de,00006h		;b82a	11 06 00 	. . . 
	add ix,de		;b82d	dd 19 	. . 
	djnz $-32		;b82f	10 de 	. . 
	ret			;b831	c9 	. 
	push iy		;b832	fd e5 	. . 
	push ix		;b834	dd e5 	. . 
	ld (ix+004h),000h		;b836	dd 36 04 00 	. 6 . . 
	ld a,(ix+003h)		;b83a	dd 7e 03 	. ~ . 
	call 01fcah		;b83d	cd ca 1f 	. . . 
	ld bc,072c7h		;b840	01 c7 72 	. . r 
	ld d,011h		;b843	16 11 	. . 
	and a			;b845	a7 	. 
	push ix		;b846	dd e5 	. . 
	pop hl			;b848	e1 	. 
	sbc hl,bc		;b849	ed 42 	. B 
	jr z,$+11		;b84b	28 09 	( . 
	ld bc,00006h		;b84d	01 06 00 	. . . 
	inc d			;b850	14 	. 
	and a			;b851	a7 	. 
	sbc hl,bc		;b852	ed 42 	. B 
	jr nz,$-4		;b854	20 fa 	  . 
	ld bc,00808h		;b856	01 08 08 	. . . 
	ld a,d			;b859	7a 	z 
	ld d,000h		;b85a	16 00 	. . 
	call 0b629h		;b85c	cd 29 b6 	. ) . 
	ld ix,072c7h		;b85f	dd 21 c7 72 	. ! . r 
	ld b,003h		;b863	06 03 	. . 
	bit 7,(ix+004h)		;b865	dd cb 04 7e 	. . . ~ 
	jr nz,$+53		;b869	20 33 	  3 
	ld de,00006h		;b86b	11 06 00 	. . . 
	add ix,de		;b86e	dd 19 	. . 
	djnz $-11		;b870	10 f3 	. . 
	jp 0d345h		;b872	c3 45 d3 	. E . 
	res 4,(hl)		;b875	cb a6 	. . 
	ld a,(072c3h)		;b877	3a c3 72 	: . r 
	bit 0,a		;b87a	cb 47 	. G 
	jr nz,$+8		;b87c	20 06 	  . 
	ld a,(072c6h)		;b87e	3a c6 72 	: . r 
	call 01fcah		;b881	cd ca 1f 	. . . 
	xor a			;b884	af 	. 
	ld (072c3h),a		;b885	32 c3 72 	2 . r 
	ld a,(072bah)		;b888	3a ba 72 	: . r 
	bit 6,a		;b88b	cb 77 	. w 
	jr z,$+14		;b88d	28 0c 	( . 
	ld hl,072c4h		;b88f	21 c4 72 	! . r 
	jp 0d300h		;b892	c3 00 d3 	. . . 
	call 01fcdh		;b895	cd cd 1f 	. . . 
	jp 0d35dh		;b898	c3 5d d3 	. ] . 
	nop			;b89b	00 	. 
	nop			;b89c	00 	. 
	nop			;b89d	00 	. 
	pop ix		;b89e	dd e1 	. . 
	pop iy		;b8a0	fd e1 	. . 
	ret			;b8a2	c9 	. 
	push ix		;b8a3	dd e5 	. . 
	push hl			;b8a5	e5 	. 
	push de			;b8a6	d5 	. 
	push bc			;b8a7	c5 	. 
	jp 0d326h		;b8a8	c3 26 d3 	. & . 
	ld ix,072c7h		;b8ab	dd 21 c7 72 	. ! . r 
	ld b,003h		;b8af	06 03 	. . 
	ld (ix+000h),010h		;b8b1	dd 36 00 10 	. 6 . . 
	ld a,(072bfh)		;b8b5	3a bf 72 	: . r 
	ld (ix+002h),a		;b8b8	dd 77 02 	. w . 
	ld a,(072beh)		;b8bb	3a be 72 	: . r 
	ld (ix+001h),a		;b8be	dd 77 01 	. w . 
	ld a,(072c1h)		;b8c1	3a c1 72 	: . r 
	and 007h		;b8c4	e6 07 	. . 
	or 080h		;b8c6	f6 80 	. . 
	ld (ix+004h),a		;b8c8	dd 77 04 	. w . 
	ld (ix+005h),000h		;b8cb	dd 36 05 00 	. 6 . . 
	push bc			;b8cf	c5 	. 
	xor a			;b8d0	af 	. 
	ld hl,00001h		;b8d1	21 01 00 	! . . 
	call 01fcdh		;b8d4	cd cd 1f 	. . . 
	ld (ix+003h),a		;b8d7	dd 77 03 	. w . 
	pop bc			;b8da	c1 	. 
	ld de,00006h		;b8db	11 06 00 	. . . 
	add ix,de		;b8de	dd 19 	. . 
	djnz $-47		;b8e0	10 cf 	. . 
	xor a			;b8e2	af 	. 
	ld hl,00078h		;b8e3	21 78 00 	! x . 
	call 01fcdh		;b8e6	cd cd 1f 	. . . 
	jp 0d36dh		;b8e9	c3 6d d3 	. m . 
	ld a,080h		;b8ec	3e 80 	> . 
	ld (072c3h),a		;b8ee	32 c3 72 	2 . r 
	pop bc			;b8f1	c1 	. 
	pop de			;b8f2	d1 	. 
	pop hl			;b8f3	e1 	. 
	pop ix		;b8f4	dd e1 	. . 
	ret			;b8f6	c9 	. 
	push iy		;b8f7	fd e5 	. . 
	ld hl,0726eh		;b8f9	21 6e 72 	! n r 
	set 7,(hl)		;b8fc	cb fe 	. . 
	bit 7,(hl)		;b8fe	cb 7e 	. ~ 
	jr nz,$-2		;b900	20 fc 	  . 
	ld hl,0b954h		;b902	21 54 b9 	! T . 
	ld de,00000h		;b905	11 00 00 	. . . 
	ld iy,0000ch		;b908	fd 21 0c 00 	. ! . . 
	ld a,004h		;b90c	3e 04 	> . 
	call 01fbeh		;b90e	cd be 1f 	. . . 
	ld hl,00000h		;b911	21 00 00 	! . . 
	dec hl			;b914	2b 	+ 
	ld a,l			;b915	7d 	} 
	or h			;b916	b4 	. 
	jr nz,$-3		;b917	20 fb 	  . 
	ld a,(0726eh)		;b919	3a 6e 72 	: n r 
	bit 1,a		;b91c	cb 4f 	. O 
	ld a,(07274h)		;b91e	3a 74 72 	: t r 
	jr z,$+5		;b921	28 03 	( . 
	ld a,(07275h)		;b923	3a 75 72 	: u r 
	cp 00bh		;b926	fe 0b 	. . 
	jr c,$+6		;b928	38 04 	8 . 
	sub 00ah		;b92a	d6 0a 	. . 
	jr $-6		;b92c	18 f8 	. . 
	dec a			;b92e	3d 	= 
	add a,a			;b92f	87 	. 
	ld c,a			;b930	4f 	O 
	ld b,000h		;b931	06 00 	. . 
	ld iy,0bf67h		;b933	fd 21 67 bf 	. ! g . 
	add iy,bc		;b937	fd 09 	. . 
	ld l,(iy+000h)		;b939	fd 6e 00 	. n . 
	ld h,(iy+001h)		;b93c	fd 66 01 	. f . 
	ld de,00000h		;b93f	11 00 00 	. . . 
	ld iy,0000ch		;b942	fd 21 0c 00 	. ! . . 
	ld a,004h		;b946	3e 04 	> . 
	call 01fbeh		;b948	cd be 1f 	. . . 
	ld bc,001e2h		;b94b	01 e2 01 	. . . 
	call 01fd9h		;b94e	cd d9 1f 	. . . 
	pop iy		;b951	fd e1 	. . 
	ret			;b953	c9 	. 
	nop			;b954	00 	. 
	add hl,de			;b955	19 	. 
	adc a,c			;b956	89 	. 
	sub b			;b957	90 	. 
	add a,b			;b958	80 	. 
	ret p			;b959	f0 	. 
	ret p			;b95a	f0 	. 
	and b			;b95b	a0 	. 
	and b			;b95c	a0 	. 
	add a,b			;b95d	80 	. 
	sbc a,c			;b95e	99 	. 
	sub b			;b95f	90 	. 
	nop			;b960	00 	. 
	ld (hl),l			;b961	75 	u 
	cp c			;b962	b9 	. 
	ld a,e			;b963	7b 	{ 
	cp c			;b964	b9 	. 
	add a,c			;b965	81 	. 
	cp c			;b966	b9 	. 
	add a,a			;b967	87 	. 
	cp c			;b968	b9 	. 
	adc a,l			;b969	8d 	. 
	cp c			;b96a	b9 	. 
	sub e			;b96b	93 	. 
	cp c			;b96c	b9 	. 
	sbc a,c			;b96d	99 	. 
	cp c			;b96e	b9 	. 
	sbc a,a			;b96f	9f 	. 
	cp c			;b970	b9 	. 
	and l			;b971	a5 	. 
	cp c			;b972	b9 	. 
	xor e			;b973	ab 	. 
	cp c			;b974	b9 	. 
	inc b			;b975	04 	. 
	rla			;b976	17 	. 
	inc (hl)			;b977	34 	4 
	dec a			;b978	3d 	= 
	ld c,e			;b979	4b 	K 
	ld l,d			;b97a	6a 	j 
	ld d,01ah		;b97b	16 1a 	. . 
	dec e			;b97d	1d 	. 
	inc h			;b97e	24 	$ 
	ld hl,(01568h)		;b97f	2a 68 15 	* h . 
	add hl,de			;b982	19 	. 
	inc hl			;b983	23 	# 
	ld b,(hl)			;b984	46 	F 
	ld l,c			;b985	69 	i 
	ld l,h			;b986	6c 	l 
	inc bc			;b987	03 	. 
	inc e			;b988	1c 	. 
	ld hl,(05639h)		;b989	2a 39 56 	* 9 V 
	ld e,(hl)			;b98c	5e 	^ 
	inc de			;b98d	13 	. 
	ld a,(de)			;b98e	1a 	. 
	inc e			;b98f	1c 	. 
	jr z,$+88		;b990	28 56 	( V 
	ld e,e			;b992	5b 	[ 
	ld d,019h		;b993	16 19 	. . 
	dec de			;b995	1b 	. 
	dec hl			;b996	2b 	+ 
	ld h,h			;b997	64 	d 
	ld l,d			;b998	6a 	j 
	inc d			;b999	14 	. 
	ld d,017h		;b99a	16 17 	. . 
	ld a,(de)			;b99c	1a 	. 
	ld e,e			;b99d	5b 	[ 
	ld h,(hl)			;b99e	66 	f 
	dec de			;b99f	1b 	. 
	inc hl			;b9a0	23 	# 
	ld h,03bh		;b9a1	26 3b 	& ; 
	ld h,a			;b9a3	67 	g 
	ld l,l			;b9a4	6d 	m 
	inc d			;b9a5	14 	. 
	rla			;b9a6	17 	. 
	inc e			;b9a7	1c 	. 
	daa			;b9a8	27 	' 
	ld a,(01967h)		;b9a9	3a 67 19 	: g . 
	dec de			;b9ac	1b 	. 
	inc h			;b9ad	24 	$ 
	ld c,h			;b9ae	4c 	L 
	ld d,e			;b9af	53 	S 
	ld l,c			;b9b0	69 	i 
	push bc			;b9b1	c5 	. 
	cp c			;b9b2	b9 	. 
	res 7,c		;b9b3	cb b9 	. . 
	pop de			;b9b5	d1 	. 
	cp c			;b9b6	b9 	. 
	rst 10h			;b9b7	d7 	. 
	cp c			;b9b8	b9 	. 
	defb 0ddh,0b9h,0e3h	;illegal sequence		;b9b9	dd b9 e3 	. . . 
	cp c			;b9bc	b9 	. 
	jp (hl)			;b9bd	e9 	. 
	cp c			;b9be	b9 	. 
	rst 28h			;b9bf	ef 	. 
	cp c			;b9c0	b9 	. 
	push af			;b9c1	f5 	. 
	cp c			;b9c2	b9 	. 
	ei			;b9c3	fb 	. 
	cp c			;b9c4	b9 	. 
	dec de			;b9c5	1b 	. 
	inc h			;b9c6	24 	$ 
	daa			;b9c7	27 	' 
	ld b,h			;b9c8	44 	D 
	ld c,h			;b9c9	4c 	L 
	ld c,l			;b9ca	4d 	M 
	rla			;b9cb	17 	. 
	add hl,de			;b9cc	19 	. 
	ld a,(de)			;b9cd	1a 	. 
	inc hl			;b9ce	23 	# 
	ld l,h			;b9cf	6c 	l 
	ld l,l			;b9d0	6d 	m 
	rla			;b9d1	17 	. 
	ld a,(de)			;b9d2	1a 	. 
	dec l			;b9d3	2d 	- 
	inc (hl)			;b9d4	34 	4 
	ld b,l			;b9d5	45 	E 
	ld l,d			;b9d6	6a 	j 
	inc b			;b9d7	04 	. 
	ld c,01bh		;b9d8	0e 1b 	. . 
	dec h			;b9da	25 	% 
	ld a,(0144ah)		;b9db	3a 4a 14 	: J . 
	jr $+31		;b9de	18 1d 	. . 
	ld d,l			;b9e0	55 	U 
	ld e,c			;b9e1	59 	Y 
	ld l,e			;b9e2	6b 	k 
	rla			;b9e3	17 	. 
	ld a,(de)			;b9e4	1a 	. 
	inc hl			;b9e5	23 	# 
	inc l			;b9e6	2c 	, 
	ld h,(hl)			;b9e7	66 	f 
	ld l,l			;b9e8	6d 	m 
	inc de			;b9e9	13 	. 
	add hl,de			;b9ea	19 	. 
	dec de			;b9eb	1b 	. 
	dec h			;b9ec	25 	% 
	ld h,l			;b9ed	65 	e 
	ld l,h			;b9ee	6c 	l 
	ld d,018h		;b9ef	16 18 	. . 
	dec hl			;b9f1	2b 	+ 
	ld (hl),066h		;b9f2	36 66 	6 f 
	ld l,e			;b9f4	6b 	k 
	rla			;b9f5	17 	. 
	inc e			;b9f6	1c 	. 
	inc h			;b9f7	24 	$ 
	dec l			;b9f8	2d 	- 
	scf			;b9f9	37 	7 
	ld l,d			;b9fa	6a 	j 
	jr $+28		;b9fb	18 1a 	. . 
	inc hl			;b9fd	23 	# 
	dec l			;b9fe	2d 	- 
	ld b,a			;b9ff	47 	G 
	ld e,h			;ba00	5c 	\ 
	dec d			;ba01	15 	. 
	cp d			;ba02	ba 	. 
	add hl,hl			;ba03	29 	) 
	cp d			;ba04	ba 	. 
	dec a			;ba05	3d 	= 
	cp d			;ba06	ba 	. 
	ld d,c			;ba07	51 	Q 
	cp d			;ba08	ba 	. 
	ld h,l			;ba09	65 	e 
	cp d			;ba0a	ba 	. 
	ld a,c			;ba0b	79 	y 
	cp d			;ba0c	ba 	. 
	adc a,l			;ba0d	8d 	. 
	cp d			;ba0e	ba 	. 
	and c			;ba0f	a1 	. 
	cp d			;ba10	ba 	. 
	or l			;ba11	b5 	. 
	cp d			;ba12	ba 	. 
	ret			;ba13	c9 	. 
	cp d			;ba14	ba 	. 
	ld l,h			;ba15	6c 	l 
	nop			;ba16	00 	. 
	ld l,h			;ba17	6c 	l 
	nop			;ba18	00 	. 
	ld l,h			;ba19	6c 	l 
	ret p			;ba1a	f0 	. 
	ld l,h			;ba1b	6c 	l 
	ret p			;ba1c	f0 	. 
	nop			;ba1d	00 	. 
	nop			;ba1e	00 	. 
	ld a,b			;ba1f	78 	x 
	jr nc,$+122		;ba20	30 78 	0 x 
	jr nc,$+2		;ba22	30 00 	0 . 
	jr nc,$+2		;ba24	30 00 	0 . 
	jr nc,$+2		;ba26	30 00 	0 . 
	nop			;ba28	00 	. 
	nop			;ba29	00 	. 
	nop			;ba2a	00 	. 
	nop			;ba2b	00 	. 
	jr nc,$+17		;ba2c	30 0f 	0 . 
	jr nc,$+113		;ba2e	30 6f 	0 o 
	jr nc,$+98		;ba30	30 60 	0 ` 
	jr nc,$+98		;ba32	30 60 	0 ` 
	ld b,060h		;ba34	06 60 	. ` 
	ld b,007h		;ba36	06 07 	. . 
	add a,(hl)			;ba38	86 	. 
	rlca			;ba39	07 	. 
	add a,(hl)			;ba3a	86 	. 
	nop			;ba3b	00 	. 
	nop			;ba3c	00 	. 
	nop			;ba3d	00 	. 
	nop			;ba3e	00 	. 
	nop			;ba3f	00 	. 
	jr nc,$+17		;ba40	30 0f 	0 . 
	jr nc,$+113		;ba42	30 6f 	0 o 
	jr nc,$+98		;ba44	30 60 	0 ` 
	jr nc,$+104		;ba46	30 66 	0 f 
	nop			;ba48	00 	. 
	ld h,(hl)			;ba49	66 	f 
	nop			;ba4a	00 	. 
	ld b,078h		;ba4b	06 78 	. x 
	ld b,078h		;ba4d	06 78 	. x 
	nop			;ba4f	00 	. 
	nop			;ba50	00 	. 
	rrca			;ba51	0f 	. 
	nop			;ba52	00 	. 
	ld l,a			;ba53	6f 	o 
	ld b,060h		;ba54	06 60 	. ` 
	ld (hl),060h		;ba56	36 60 	6 ` 
	ld (hl),060h		;ba58	36 60 	6 ` 
	ld (hl),000h		;ba5a	36 00 	6 . 
	jr nc,$+2		;ba5c	30 00 	0 . 
	nop			;ba5e	00 	. 
	nop			;ba5f	00 	. 
	nop			;ba60	00 	. 
	ld e,000h		;ba61	1e 00 	. . 
	ld e,000h		;ba63	1e 00 	. . 
	nop			;ba65	00 	. 
	nop			;ba66	00 	. 
	nop			;ba67	00 	. 
	nop			;ba68	00 	. 
	ld e,03ch		;ba69	1e 3c 	. < 
	ld e,03ch		;ba6b	1e 3c 	. < 
	nop			;ba6d	00 	. 
	nop			;ba6e	00 	. 
	jr nc,$+26		;ba6f	30 18 	0 . 
	inc sp			;ba71	33 	3 
	ret c			;ba72	d8 	. 
	inc sp			;ba73	33 	3 
	ret c			;ba74	d8 	. 
	jr nc,$+26		;ba75	30 18 	0 . 
	nop			;ba77	00 	. 
	nop			;ba78	00 	. 
	nop			;ba79	00 	. 
	nop			;ba7a	00 	. 
	jr $+14		;ba7b	18 0c 	. . 
	dec de			;ba7d	1b 	. 
	call z,0cc1bh		;ba7e	cc 1b cc 	. . . 
	jr $+14		;ba81	18 0c 	. . 
	nop			;ba83	00 	. 
	nop			;ba84	00 	. 
	nop			;ba85	00 	. 
	nop			;ba86	00 	. 
	ld e,078h		;ba87	1e 78 	. x 
	ld e,078h		;ba89	1e 78 	. x 
	nop			;ba8b	00 	. 
	nop			;ba8c	00 	. 
	nop			;ba8d	00 	. 
	nop			;ba8e	00 	. 
	nop			;ba8f	00 	. 
	nop			;ba90	00 	. 
	inc sp			;ba91	33 	3 
	ret nz			;ba92	c0 	. 
	inc sp			;ba93	33 	3 
	ret nz			;ba94	c0 	. 
	jr nc,$+2		;ba95	30 00 	0 . 
	jr nc,$+14		;ba97	30 0c 	0 . 
	nop			;ba99	00 	. 
	ld l,h			;ba9a	6c 	l 
	inc a			;ba9b	3c 	< 
	ld l,h			;ba9c	6c 	l 
	inc a			;ba9d	3c 	< 
	ld l,h			;ba9e	6c 	l 
	nop			;ba9f	00 	. 
	ld h,b			;baa0	60 	` 
	nop			;baa1	00 	. 
	nop			;baa2	00 	. 
	jr $-38		;baa3	18 d8 	. . 
	jr $-38		;baa5	18 d8 	. . 
	jr $-38		;baa7	18 d8 	. . 
	jr $-38		;baa9	18 d8 	. . 
	nop			;baab	00 	. 
	nop			;baac	00 	. 
	nop			;baad	00 	. 
	nop			;baae	00 	. 
	ld e,078h		;baaf	1e 78 	. x 
	ld e,078h		;bab1	1e 78 	. x 
	nop			;bab3	00 	. 
	nop			;bab4	00 	. 
	nop			;bab5	00 	. 
	nop			;bab6	00 	. 
	dec c			;bab7	0d 	. 
	ret po			;bab8	e0 	. 
	dec c			;bab9	0d 	. 
	ret po			;baba	e0 	. 
	inc c			;babb	0c 	. 
	inc a			;babc	3c 	< 
	inc c			;babd	0c 	. 
	inc a			;babe	3c 	< 
	ld h,b			;babf	60 	` 
	nop			;bac0	00 	. 
	ld h,b			;bac1	60 	` 
	nop			;bac2	00 	. 
	ld h,b			;bac3	60 	` 
	ret p			;bac4	f0 	. 
	ld h,b			;bac5	60 	` 
	ret p			;bac6	f0 	. 
	nop			;bac7	00 	. 
	nop			;bac8	00 	. 
	nop			;bac9	00 	. 
	nop			;baca	00 	. 
	nop			;bacb	00 	. 
	nop			;bacc	00 	. 
	nop			;bacd	00 	. 
	ret p			;bace	f0 	. 
	inc a			;bacf	3c 	< 
	ret p			;bad0	f0 	. 
	inc a			;bad1	3c 	< 
	inc c			;bad2	0c 	. 
	ld e,00ch		;bad3	1e 0c 	. . 
	ld e,00ch		;bad5	1e 0c 	. . 
	inc bc			;bad7	03 	. 
	call z,0c003h		;bad8	cc 03 c0 	. . . 
	nop			;badb	00 	. 
	nop			;badc	00 	. 
	pop af			;badd	f1 	. 
	cp d			;bade	ba 	. 
	ld e,d			;badf	5a 	Z 
	cp e			;bae0	bb 	. 
	and h			;bae1	a4 	. 
	cp e			;bae2	bb 	. 
	rst 28h			;bae3	ef 	. 
	cp e			;bae4	bb 	. 
	ld c,c			;bae5	49 	I 
	cp h			;bae6	bc 	. 
	add a,c			;bae7	81 	. 
	cp h			;bae8	bc 	. 
	jp z,004bch		;bae9	ca bc 04 	. . . 
	cp l			;baec	bd 	. 
	ld h,c			;baed	61 	a 
	cp l			;baee	bd 	. 
	or b			;baef	b0 	. 
	cp l			;baf0	bd 	. 
	ld bc,00600h		;baf1	01 00 06 	. . . 
	ld c,a			;baf4	4f 	O 
	rst 28h			;baf5	ef 	. 
	ld bc,004cfh		;baf6	01 cf 04 	. . . 
	xor a			;baf9	af 	. 
	ld bc,00a00h		;bafa	01 00 0a 	. . . 
	ccf			;bafd	3f 	? 
	ld bc,00400h		;bafe	01 00 04 	. . . 
	ld e,a			;bb01	5f 	_ 
	xor a			;bb02	af 	. 
	ld bc,00900h		;bb03	01 00 09 	. . . 
	ccf			;bb06	3f 	? 
	ld bc,00500h		;bb07	01 00 05 	. . . 
	ld e,a			;bb0a	5f 	_ 
	xor a			;bb0b	af 	. 
	ld bc,00800h		;bb0c	01 00 08 	. . . 
	ccf			;bb0f	3f 	? 
	ld bc,00600h		;bb10	01 00 06 	. . . 
	ccf			;bb13	3f 	? 
	ld bc,00800h		;bb14	01 00 08 	. . . 
	ccf			;bb17	3f 	? 
	ld bc,00600h		;bb18	01 00 06 	. . . 
	ccf			;bb1b	3f 	? 
	ld bc,00800h		;bb1c	01 00 08 	. . . 
	ccf			;bb1f	3f 	? 
	ld bc,00600h		;bb20	01 00 06 	. . . 
	ccf			;bb23	3f 	? 
	ld bc,00800h		;bb24	01 00 08 	. . . 
	ccf			;bb27	3f 	? 
	ld bc,00600h		;bb28	01 00 06 	. . . 
	ccf			;bb2b	3f 	? 
	nop			;bb2c	00 	. 
	nop			;bb2d	00 	. 
	ld l,a			;bb2e	6f 	o 
	rst 8			;bb2f	cf 	. 
	xor a			;bb30	af 	. 
	ld bc,00300h		;bb31	01 00 03 	. . . 
	ccf			;bb34	3f 	? 
	ld bc,00500h		;bb35	01 00 05 	. . . 
	ld l,a			;bb38	6f 	o 
	sbc a,a			;bb39	9f 	. 
	nop			;bb3a	00 	. 
	nop			;bb3b	00 	. 
	ccf			;bb3c	3f 	? 
	nop			;bb3d	00 	. 
	ccf			;bb3e	3f 	? 
	ld bc,00300h		;bb3f	01 00 03 	. . . 
	ccf			;bb42	3f 	? 
	ld bc,00400h		;bb43	01 00 04 	. . . 
	ld l,a			;bb46	6f 	o 
	sbc a,a			;bb47	9f 	. 
	ld bc,00300h		;bb48	01 00 03 	. . . 
	ld e,a			;bb4b	5f 	_ 
	rst 8			;bb4c	cf 	. 
	rst 18h			;bb4d	df 	. 
	ld bc,003cfh		;bb4e	01 cf 03 	. . . 
	rst 18h			;bb51	df 	. 
	ld bc,004cfh		;bb52	01 cf 04 	. . . 
	sbc a,a			;bb55	9f 	. 
	ld bc,00300h		;bb56	01 00 03 	. . . 
	ld (bc),a			;bb59	02 	. 
	nop			;bb5a	00 	. 
	nop			;bb5b	00 	. 
	ld l,a			;bb5c	6f 	o 
	ld bc,00acfh		;bb5d	01 cf 0a 	. . . 
	xor a			;bb60	af 	. 
	ld bc,00300h		;bb61	01 00 03 	. . . 
	ld l,a			;bb64	6f 	o 
	sbc a,a			;bb65	9f 	. 
	ld bc,00a00h		;bb66	01 00 0a 	. . . 
	ld e,a			;bb69	5f 	_ 
	xor a			;bb6a	af 	. 
	nop			;bb6b	00 	. 
	nop			;bb6c	00 	. 
	rra			;bb6d	1f 	. 
	ld bc,00c00h		;bb6e	01 00 0c 	. . . 
	ccf			;bb71	3f 	? 
	ld bc,00e00h		;bb72	01 00 0e 	. . . 
	ld l,a			;bb75	6f 	o 
	sbc a,a			;bb76	9f 	. 
	ld bc,00800h		;bb77	01 00 08 	. . . 
	cpl			;bb7a	2f 	/ 
	ld bc,00400h		;bb7b	01 00 04 	. . . 
	ld l,a			;bb7e	6f 	o 
	sbc a,a			;bb7f	9f 	. 
	ld bc,00600h		;bb80	01 00 06 	. . . 
	ld l,a			;bb83	6f 	o 
	rst 8			;bb84	cf 	. 
	rst 8			;bb85	cf 	. 
	rst 18h			;bb86	df 	. 
	ld bc,004cfh		;bb87	01 cf 04 	. . . 
	sbc a,a			;bb8a	9f 	. 
	ld bc,00600h		;bb8b	01 00 06 	. . . 
	ld l,a			;bb8e	6f 	o 
	sbc a,a			;bb8f	9f 	. 
	ld bc,00c00h		;bb90	01 00 0c 	. . . 
	ld l,a			;bb93	6f 	o 
	rst 8			;bb94	cf 	. 
	sbc a,a			;bb95	9f 	. 
	ld bc,00d00h		;bb96	01 00 0d 	. . . 
	ccf			;bb99	3f 	? 
	ld bc,00f00h		;bb9a	01 00 0f 	. . . 
	ld e,a			;bb9d	5f 	_ 
	ld bc,00ccfh		;bb9e	01 cf 0c 	. . . 
	adc a,a			;bba1	8f 	. 
	nop			;bba2	00 	. 
	ld (bc),a			;bba3	02 	. 
	nop			;bba4	00 	. 
	nop			;bba5	00 	. 
	ld l,a			;bba6	6f 	o 
	ld bc,00acfh		;bba7	01 cf 0a 	. . . 
	xor a			;bbaa	af 	. 
	ld bc,00300h		;bbab	01 00 03 	. . . 
	ld l,a			;bbae	6f 	o 
	sbc a,a			;bbaf	9f 	. 
	ld bc,00a00h		;bbb0	01 00 0a 	. . . 
	ld e,a			;bbb3	5f 	_ 
	xor a			;bbb4	af 	. 
	nop			;bbb5	00 	. 
	nop			;bbb6	00 	. 
	rra			;bbb7	1f 	. 
	ld bc,00c00h		;bbb8	01 00 0c 	. . . 
	ccf			;bbbb	3f 	? 
	ld bc,00f00h		;bbbc	01 00 0f 	. . . 
	ccf			;bbbf	3f 	? 
	ld bc,00800h		;bbc0	01 00 08 	. . . 
	cpl			;bbc3	2f 	/ 
	ld bc,00600h		;bbc4	01 00 06 	. . . 
	ccf			;bbc7	3f 	? 
	ld bc,00800h		;bbc8	01 00 08 	. . . 
	ld e,a			;bbcb	5f 	_ 
	ld bc,006cfh		;bbcc	01 cf 06 	. . . 
	cp a			;bbcf	bf 	. 
	ld bc,00f00h		;bbd0	01 00 0f 	. . . 
	ccf			;bbd3	3f 	? 
	nop			;bbd4	00 	. 
	nop			;bbd5	00 	. 
	cpl			;bbd6	2f 	/ 
	ld bc,00c00h		;bbd7	01 00 0c 	. . . 
	ccf			;bbda	3f 	? 
	nop			;bbdb	00 	. 
	nop			;bbdc	00 	. 
	ld e,a			;bbdd	5f 	_ 
	xor a			;bbde	af 	. 
	ld bc,00a00h		;bbdf	01 00 0a 	. . . 
	ld l,a			;bbe2	6f 	o 
	sbc a,a			;bbe3	9f 	. 
	ld bc,00300h		;bbe4	01 00 03 	. . . 
	ld e,a			;bbe7	5f 	_ 
	ld bc,00acfh		;bbe8	01 cf 0a 	. . . 
	sbc a,a			;bbeb	9f 	. 
	nop			;bbec	00 	. 
	nop			;bbed	00 	. 
	ld (bc),a			;bbee	02 	. 
	ld bc,00900h		;bbef	01 00 09 	. . . 
	ld l,a			;bbf2	6f 	o 
	rst 8			;bbf3	cf 	. 
	rst 8			;bbf4	cf 	. 
	xor a			;bbf5	af 	. 
	ld bc,00b00h		;bbf6	01 00 0b 	. . . 
	ld l,a			;bbf9	6f 	o 
	sbc a,a			;bbfa	9f 	. 
	nop			;bbfb	00 	. 
	nop			;bbfc	00 	. 
	ccf			;bbfd	3f 	? 
	ld bc,00800h		;bbfe	01 00 08 	. . . 
	ld l,a			;bc01	6f 	o 
	rst 8			;bc02	cf 	. 
	rst 8			;bc03	cf 	. 
	sbc a,a			;bc04	9f 	. 
	ld bc,00300h		;bc05	01 00 03 	. . . 
	ccf			;bc08	3f 	? 
	ld bc,00800h		;bc09	01 00 08 	. . . 
	ccf			;bc0c	3f 	? 
	ld bc,00600h		;bc0d	01 00 06 	. . . 
	ccf			;bc10	3f 	? 
	ld bc,00600h		;bc11	01 00 06 	. . . 
	ld l,a			;bc14	6f 	o 
	rst 8			;bc15	cf 	. 
	rst 18h			;bc16	df 	. 
	rst 8			;bc17	cf 	. 
	adc a,a			;bc18	8f 	. 
	ld bc,00400h		;bc19	01 00 04 	. . . 
	ccf			;bc1c	3f 	? 
	ld bc,00400h		;bc1d	01 00 04 	. . . 
	ld l,a			;bc20	6f 	o 
	rst 8			;bc21	cf 	. 
	sbc a,a			;bc22	9f 	. 
	ld bc,00800h		;bc23	01 00 08 	. . . 
	ccf			;bc26	3f 	? 
	ld bc,00400h		;bc27	01 00 04 	. . . 
	ccf			;bc2a	3f 	? 
	ld bc,00a00h		;bc2b	01 00 0a 	. . . 
	ccf			;bc2e	3f 	? 
	ld bc,00400h		;bc2f	01 00 04 	. . . 
	ld e,a			;bc32	5f 	_ 
	ld bc,00acfh		;bc33	01 cf 0a 	. . . 
	rst 38h			;bc36	ff 	. 
	rst 8			;bc37	cf 	. 
	adc a,a			;bc38	8f 	. 
	ld bc,00d00h		;bc39	01 00 0d 	. . . 
	ccf			;bc3c	3f 	? 
	ld bc,00a00h		;bc3d	01 00 0a 	. . . 
	ld c,a			;bc40	4f 	O 
	ld bc,004cfh		;bc41	01 cf 04 	. . . 
	sbc a,a			;bc44	9f 	. 
	ld bc,00300h		;bc45	01 00 03 	. . . 
	ld (bc),a			;bc48	02 	. 
	nop			;bc49	00 	. 
	ld l,a			;bc4a	6f 	o 
	ld bc,00ccfh		;bc4b	01 cf 0c 	. . . 
	adc a,a			;bc4e	8f 	. 
	nop			;bc4f	00 	. 
	nop			;bc50	00 	. 
	ccf			;bc51	3f 	? 
	ld bc,00f00h		;bc52	01 00 0f 	. . . 
	ccf			;bc55	3f 	? 
	ld bc,00f00h		;bc56	01 00 0f 	. . . 
	ccf			;bc59	3f 	? 
	ld bc,00f00h		;bc5a	01 00 0f 	. . . 
	ld e,a			;bc5d	5f 	_ 
	ld bc,00bcfh		;bc5e	01 cf 0b 	. . . 
	xor a			;bc61	af 	. 
	ld bc,00f00h		;bc62	01 00 0f 	. . . 
	ld e,a			;bc65	5f 	_ 
	xor a			;bc66	af 	. 
	ld bc,00f00h		;bc67	01 00 0f 	. . . 
	ccf			;bc6a	3f 	? 
	ld bc,00f00h		;bc6b	01 00 0f 	. . . 
	ccf			;bc6e	3f 	? 
	nop			;bc6f	00 	. 
	nop			;bc70	00 	. 
	cpl			;bc71	2f 	/ 
	ld bc,00b00h		;bc72	01 00 0b 	. . . 
	ld l,a			;bc75	6f 	o 
	sbc a,a			;bc76	9f 	. 
	nop			;bc77	00 	. 
	nop			;bc78	00 	. 
	ld e,a			;bc79	5f 	_ 
	ld bc,00bcfh		;bc7a	01 cf 0b 	. . . 
	sbc a,a			;bc7d	9f 	. 
	nop			;bc7e	00 	. 
	nop			;bc7f	00 	. 
	ld (bc),a			;bc80	02 	. 
	nop			;bc81	00 	. 
	nop			;bc82	00 	. 
	ld l,a			;bc83	6f 	o 
	ld bc,00bcfh		;bc84	01 cf 0b 	. . . 
	adc a,a			;bc87	8f 	. 
	nop			;bc88	00 	. 
	nop			;bc89	00 	. 
	ld l,a			;bc8a	6f 	o 
	sbc a,a			;bc8b	9f 	. 
	ld bc,00e00h		;bc8c	01 00 0e 	. . . 
	ccf			;bc8f	3f 	? 
	ld bc,00f00h		;bc90	01 00 0f 	. . . 
	ccf			;bc93	3f 	? 
	ld bc,00f00h		;bc94	01 00 0f 	. . . 
	ccf			;bc97	3f 	? 
	ld bc,00500h		;bc98	01 00 05 	. . . 
	cpl			;bc9b	2f 	/ 
	ld bc,00900h		;bc9c	01 00 09 	. . . 
	ld a,a			;bc9f	7f 	 
	ld bc,005cfh		;bca0	01 cf 05 	. . . 
	rst 18h			;bca3	df 	. 
	ld bc,006cfh		;bca4	01 cf 06 	. . . 
	xor a			;bca7	af 	. 
	nop			;bca8	00 	. 
	nop			;bca9	00 	. 
	ccf			;bcaa	3f 	? 
	ld bc,00c00h		;bcab	01 00 0c 	. . . 
	ccf			;bcae	3f 	? 
	nop			;bcaf	00 	. 
	nop			;bcb0	00 	. 
	ccf			;bcb1	3f 	? 
	ld bc,00c00h		;bcb2	01 00 0c 	. . . 
	ccf			;bcb5	3f 	? 
	nop			;bcb6	00 	. 
	nop			;bcb7	00 	. 
	ld e,a			;bcb8	5f 	_ 
	xor a			;bcb9	af 	. 
	ld bc,00a00h		;bcba	01 00 0a 	. . . 
	ld l,a			;bcbd	6f 	o 
	sbc a,a			;bcbe	9f 	. 
	ld bc,00300h		;bcbf	01 00 03 	. . . 
	ld e,a			;bcc2	5f 	_ 
	ld bc,00acfh		;bcc3	01 cf 0a 	. . . 
	sbc a,a			;bcc6	9f 	. 
	nop			;bcc7	00 	. 
	nop			;bcc8	00 	. 
	ld (bc),a			;bcc9	02 	. 
	nop			;bcca	00 	. 
	ld l,a			;bccb	6f 	o 
	ld bc,00ccfh		;bccc	01 cf 0c 	. . . 
	xor a			;bccf	af 	. 
	nop			;bcd0	00 	. 
	nop			;bcd1	00 	. 
	rra			;bcd2	1f 	. 
	ld bc,00c00h		;bcd3	01 00 0c 	. . . 
	ccf			;bcd6	3f 	? 
	ld bc,00e00h		;bcd7	01 00 0e 	. . . 
	ld l,a			;bcda	6f 	o 
	sbc a,a			;bcdb	9f 	. 
	ld bc,00c00h		;bcdc	01 00 0c 	. . . 
	ld l,a			;bcdf	6f 	o 
	rst 8			;bce0	cf 	. 
	sbc a,a			;bce1	9f 	. 
	ld bc,00900h		;bce2	01 00 09 	. . . 
	cpl			;bce5	2f 	/ 
	nop			;bce6	00 	. 
	ld l,a			;bce7	6f 	o 
	rst 8			;bce8	cf 	. 
	sbc a,a			;bce9	9f 	. 
	ld bc,00b00h		;bcea	01 00 0b 	. . . 
	ld a,a			;bced	7f 	 
	rst 8			;bcee	cf 	. 
	sbc a,a			;bcef	9f 	. 
	ld bc,00d00h		;bcf0	01 00 0d 	. . . 
	ccf			;bcf3	3f 	? 
	ld bc,00f00h		;bcf4	01 00 0f 	. . . 
	ccf			;bcf7	3f 	? 
	ld bc,00f00h		;bcf8	01 00 0f 	. . . 
	ccf			;bcfb	3f 	? 
	ld bc,00f00h		;bcfc	01 00 0f 	. . . 
	rra			;bcff	1f 	. 
	ld bc,00800h		;bd00	01 00 08 	. . . 
	ld (bc),a			;bd03	02 	. 
	nop			;bd04	00 	. 
	nop			;bd05	00 	. 
	ld l,a			;bd06	6f 	o 
	ld bc,00acfh		;bd07	01 cf 0a 	. . . 
	xor a			;bd0a	af 	. 
	ld bc,00300h		;bd0b	01 00 03 	. . . 
	ld l,a			;bd0e	6f 	o 
	sbc a,a			;bd0f	9f 	. 
	ld bc,00a00h		;bd10	01 00 0a 	. . . 
	ld e,a			;bd13	5f 	_ 
	xor a			;bd14	af 	. 
	nop			;bd15	00 	. 
	nop			;bd16	00 	. 
	ccf			;bd17	3f 	? 
	ld bc,00c00h		;bd18	01 00 0c 	. . . 
	ccf			;bd1b	3f 	? 
	nop			;bd1c	00 	. 
	nop			;bd1d	00 	. 
	ccf			;bd1e	3f 	? 
	ld bc,00c00h		;bd1f	01 00 0c 	. . . 
	ccf			;bd22	3f 	? 
	nop			;bd23	00 	. 
	nop			;bd24	00 	. 
	ld e,a			;bd25	5f 	_ 
	xor a			;bd26	af 	. 
	ld bc,00400h		;bd27	01 00 04 	. . . 
	cpl			;bd2a	2f 	/ 
	ld bc,00500h		;bd2b	01 00 05 	. . . 
	ld l,a			;bd2e	6f 	o 
	sbc a,a			;bd2f	9f 	. 
	ld bc,00300h		;bd30	01 00 03 	. . . 
	ld a,a			;bd33	7f 	 
	ld bc,004cfh		;bd34	01 cf 04 	. . . 
	rst 18h			;bd37	df 	. 
	ld bc,005cfh		;bd38	01 cf 05 	. . . 
	cp a			;bd3b	bf 	. 
	ld bc,00300h		;bd3c	01 00 03 	. . . 
	ld l,a			;bd3f	6f 	o 
	sbc a,a			;bd40	9f 	. 
	ld bc,00a00h		;bd41	01 00 0a 	. . . 
	ld e,a			;bd44	5f 	_ 
	xor a			;bd45	af 	. 
	nop			;bd46	00 	. 
	nop			;bd47	00 	. 
	ccf			;bd48	3f 	? 
	ld bc,00c00h		;bd49	01 00 0c 	. . . 
	ccf			;bd4c	3f 	? 
	nop			;bd4d	00 	. 
	nop			;bd4e	00 	. 
	ld e,a			;bd4f	5f 	_ 
	xor a			;bd50	af 	. 
	ld bc,00a00h		;bd51	01 00 0a 	. . . 
	ld l,a			;bd54	6f 	o 
	sbc a,a			;bd55	9f 	. 
	ld bc,00300h		;bd56	01 00 03 	. . . 
	ld e,a			;bd59	5f 	_ 
	ld bc,00acfh		;bd5a	01 cf 0a 	. . . 
	sbc a,a			;bd5d	9f 	. 
	nop			;bd5e	00 	. 
	nop			;bd5f	00 	. 
	ld (bc),a			;bd60	02 	. 
	nop			;bd61	00 	. 
	nop			;bd62	00 	. 
	ld l,a			;bd63	6f 	o 
	ld bc,00acfh		;bd64	01 cf 0a 	. . . 
	xor a			;bd67	af 	. 
	ld bc,00300h		;bd68	01 00 03 	. . . 
	ld l,a			;bd6b	6f 	o 
	sbc a,a			;bd6c	9f 	. 
	ld bc,00a00h		;bd6d	01 00 0a 	. . . 
	ld e,a			;bd70	5f 	_ 
	xor a			;bd71	af 	. 
	nop			;bd72	00 	. 
	nop			;bd73	00 	. 
	ccf			;bd74	3f 	? 
	ld bc,00c00h		;bd75	01 00 0c 	. . . 
	ccf			;bd78	3f 	? 
	nop			;bd79	00 	. 
	nop			;bd7a	00 	. 
	ccf			;bd7b	3f 	? 
	ld bc,00c00h		;bd7c	01 00 0c 	. . . 
	ccf			;bd7f	3f 	? 
	nop			;bd80	00 	. 
	nop			;bd81	00 	. 
	ld e,a			;bd82	5f 	_ 
	rst 8			;bd83	cf 	. 
	xor a			;bd84	af 	. 
	ld bc,00300h		;bd85	01 00 03 	. . . 
	cpl			;bd88	2f 	/ 
	ld bc,00600h		;bd89	01 00 06 	. . . 
	ccf			;bd8c	3f 	? 
	ld bc,00400h		;bd8d	01 00 04 	. . . 
	ld e,a			;bd90	5f 	_ 
	ld bc,003cfh		;bd91	01 cf 03 	. . . 
	rst 18h			;bd94	df 	. 
	ld bc,006cfh		;bd95	01 cf 06 	. . . 
	cp a			;bd98	bf 	. 
	ld bc,00f00h		;bd99	01 00 0f 	. . . 
	ccf			;bd9c	3f 	? 
	ld bc,00f00h		;bd9d	01 00 0f 	. . . 
	ccf			;bda0	3f 	? 
	ld bc,00e00h		;bda1	01 00 0e 	. . . 
	ld l,a			;bda4	6f 	o 
	sbc a,a			;bda5	9f 	. 
	nop			;bda6	00 	. 
	nop			;bda7	00 	. 
	ld c,a			;bda8	4f 	O 
	ld bc,00bcfh		;bda9	01 cf 0b 	. . . 
	sbc a,a			;bdac	9f 	. 
	nop			;bdad	00 	. 
	nop			;bdae	00 	. 
	ld (bc),a			;bdaf	02 	. 
	nop			;bdb0	00 	. 
	nop			;bdb1	00 	. 
	ld l,a			;bdb2	6f 	o 
	ld bc,00acfh		;bdb3	01 cf 0a 	. . . 
	xor a			;bdb6	af 	. 
	ld bc,00300h		;bdb7	01 00 03 	. . . 
	ld l,a			;bdba	6f 	o 
	rst 18h			;bdbb	df 	. 
	rst 8			;bdbc	cf 	. 
	xor a			;bdbd	af 	. 
	ld bc,00800h		;bdbe	01 00 08 	. . . 
	ld e,a			;bdc1	5f 	_ 
	xor a			;bdc2	af 	. 
	nop			;bdc3	00 	. 
	nop			;bdc4	00 	. 
	ccf			;bdc5	3f 	? 
	nop			;bdc6	00 	. 
	nop			;bdc7	00 	. 
	ld e,a			;bdc8	5f 	_ 
	rst 8			;bdc9	cf 	. 
	xor a			;bdca	af 	. 
	ld bc,00700h		;bdcb	01 00 07 	. . . 
	ccf			;bdce	3f 	? 
	nop			;bdcf	00 	. 
	nop			;bdd0	00 	. 
	ccf			;bdd1	3f 	? 
	ld bc,00400h		;bdd2	01 00 04 	. . . 
	ld e,a			;bdd5	5f 	_ 
	xor a			;bdd6	af 	. 
	ld bc,00600h		;bdd7	01 00 06 	. . . 
	ccf			;bdda	3f 	? 
	nop			;bddb	00 	. 
	nop			;bddc	00 	. 
	ccf			;bddd	3f 	? 
	ld bc,00500h		;bdde	01 00 05 	. . . 
	ld e,a			;bde1	5f 	_ 
	xor a			;bde2	af 	. 
	ld bc,00500h		;bde3	01 00 05 	. . . 
	ccf			;bde6	3f 	? 
	nop			;bde7	00 	. 
	nop			;bde8	00 	. 
	ccf			;bde9	3f 	? 
	ld bc,00600h		;bdea	01 00 06 	. . . 
	ld e,a			;bded	5f 	_ 
	xor a			;bdee	af 	. 
	ld bc,00400h		;bdef	01 00 04 	. . . 
	ccf			;bdf2	3f 	? 
	nop			;bdf3	00 	. 
	nop			;bdf4	00 	. 
	ccf			;bdf5	3f 	? 
	ld bc,00700h		;bdf6	01 00 07 	. . . 
	ld e,a			;bdf9	5f 	_ 
	xor a			;bdfa	af 	. 
	ld bc,00300h		;bdfb	01 00 03 	. . . 
	ccf			;bdfe	3f 	? 
	nop			;bdff	00 	. 
	nop			;be00	00 	. 
	ccf			;be01	3f 	? 
	ld bc,00800h		;be02	01 00 08 	. . . 
	ld e,a			;be05	5f 	_ 
	xor a			;be06	af 	. 
	nop			;be07	00 	. 
	nop			;be08	00 	. 
	ccf			;be09	3f 	? 
	nop			;be0a	00 	. 
	nop			;be0b	00 	. 
	ld e,a			;be0c	5f 	_ 
	xor a			;be0d	af 	. 
	ld bc,00800h		;be0e	01 00 08 	. . . 
	ld e,a			;be11	5f 	_ 
	rst 8			;be12	cf 	. 
	rst 28h			;be13	ef 	. 
	sbc a,a			;be14	9f 	. 
	ld bc,00300h		;be15	01 00 03 	. . . 
	ld e,a			;be18	5f 	_ 
	ld bc,00acfh		;be19	01 cf 0a 	. . . 
	sbc a,a			;be1c	9f 	. 
	nop			;be1d	00 	. 
	nop			;be1e	00 	. 
	ld (bc),a			;be1f	02 	. 
	nop			;be20	00 	. 
	ld hl,00a00h		;be21	21 00 0a 	! . . 
	nop			;be24	00 	. 
	ld l,(hl)			;be25	6e 	n 
	ld bc,00188h		;be26	01 88 01 	. . . 
	adc a,b			;be29	88 	. 
	ld bc,00148h		;be2a	01 48 01 	. H . 
	ld h,(hl)			;be2d	66 	f 
	ld bc,00166h		;be2e	01 66 01 	. f . 
	ld l,d			;be31	6a 	j 
	ld bc,0016eh		;be32	01 6e 01 	. n . 
	ld l,(hl)			;be35	6e 	n 
	ld bc,0016eh		;be36	01 6e 01 	. n . 
	ld l,(hl)			;be39	6e 	n 
	ld bc,0016eh		;be3a	01 6e 01 	. n . 
	ld b,c			;be3d	41 	A 
	nop			;be3e	00 	. 
	nop			;be3f	00 	. 
	nop			;be40	00 	. 
	nop			;be41	00 	. 
	nop			;be42	00 	. 
	nop			;be43	00 	. 
	nop			;be44	00 	. 
	nop			;be45	00 	. 
	nop			;be46	00 	. 
	nop			;be47	00 	. 
	nop			;be48	00 	. 
	ld (hl),c			;be49	71 	q 
	cp (hl)			;be4a	be 	. 
	ld a,c			;be4b	79 	y 
	cp (hl)			;be4c	be 	. 
	adc a,h			;be4d	8c 	. 
	cp (hl)			;be4e	be 	. 
	sub e			;be4f	93 	. 
	cp (hl)			;be50	be 	. 
	and (hl)			;be51	a6 	. 
	cp (hl)			;be52	be 	. 
	cp c			;be53	b9 	. 
	cp (hl)			;be54	be 	. 
	call pe,00bbeh		;be55	ec be 0b 	. . . 
	cp a			;be58	bf 	. 
	ld hl,(040bfh)		;be59	2a bf 40 	* . @ 
	cp a			;be5c	bf 	. 
	ld b,a			;be5d	47 	G 
	cp a			;be5e	bf 	. 
	ld c,(hl)			;be5f	4e 	N 
	cp a			;be60	bf 	. 
	ld d,l			;be61	55 	U 
	cp a			;be62	bf 	. 
	ld e,h			;be63	5c 	\ 
	cp a			;be64	bf 	. 
	ld h,e			;be65	63 	c 
	cp a			;be66	bf 	. 
	nop			;be67	00 	. 
	nop			;be68	00 	. 
	nop			;be69	00 	. 
	nop			;be6a	00 	. 
	nop			;be6b	00 	. 
	nop			;be6c	00 	. 
	nop			;be6d	00 	. 
	nop			;be6e	00 	. 
	nop			;be6f	00 	. 
	nop			;be70	00 	. 
	ld b,d			;be71	42 	B 
	ld b,e			;be72	43 	C 
	ld b,h			;be73	44 	D 
	cp 017h		;be74	fe 17 	. . 
	pop af			;be76	f1 	. 
	jp (hl)			;be77	e9 	. 
	rst 38h			;be78	ff 	. 
	ld a,(009fdh)		;be79	3a fd 09 	: . . 
	dec a			;be7c	3d 	= 
	ccf			;be7d	3f 	? 
	cp 015h		;be7e	fe 15 	. . 
	dec sp			;be80	3b 	; 
	cp 009h		;be81	fe 09 	. . 
	ld b,b			;be83	40 	@ 
	cp 015h		;be84	fe 15 	. . 
	inc a			;be86	3c 	< 
	add iy,bc		;be87	fd 09 	. . 
	ld a,041h		;be89	3e 41 	> A 
	rst 38h			;be8b	ff 	. 
	ld (hl),b			;be8c	70 	p 
	ld (hl),d			;be8d	72 	r 
	cp 01eh		;be8e	fe 1e 	. . 
	ld (hl),c			;be90	71 	q 
	ld (hl),e			;be91	73 	s 
	rst 38h			;be92	ff 	. 
	ret pe			;be93	e8 	. 
	and 0f5h		;be94	e6 f5 	. . 
	nop			;be96	00 	. 
	di			;be97	f3 	. 
	and 0e2h		;be98	e6 e2 	. . 
	push hl			;be9a	e5 	. 
	jp m,0f100h		;be9b	fa 00 f1 	. . . 
	defb 0edh;next byte illegal after ed		;be9e	ed 	. 
	jp po,0e6fah		;be9f	e2 fa e6 	. . . 
	di			;bea2	f3 	. 
	nop			;bea3	00 	. 
	exx			;bea4	d9 	. 
	rst 38h			;bea5	ff 	. 
	ret pe			;bea6	e8 	. 
	and 0f5h		;bea7	e6 f5 	. . 
	nop			;bea9	00 	. 
	di			;beaa	f3 	. 
	and 0e2h		;beab	e6 e2 	. . 
	push hl			;bead	e5 	. 
	jp m,0f100h		;beae	fa 00 f1 	. . . 
	defb 0edh;next byte illegal after ed		;beb1	ed 	. 
	jp po,0e6fah		;beb2	e2 fa e6 	. . . 
	di			;beb5	f3 	. 
	nop			;beb6	00 	. 
	jp c,0e4ffh		;beb7	da ff e4 	. . . 
	ret p			;beba	f0 	. 
	rst 28h			;bebb	ef 	. 
	ret pe			;bebc	e8 	. 
	di			;bebd	f3 	. 
	jp po,0f6f5h		;bebe	e2 f5 f6 	. . . 
	defb 0edh;next byte illegal after ed		;bec1	ed 	. 
	jp po,0eaf5h		;bec2	e2 f5 ea 	. . . 
	ret p			;bec5	f0 	. 
	rst 28h			;bec6	ef 	. 
	call p,0fd00h		;bec7	f4 00 fd 	. . . 
	ld bc,0feffh		;beca	01 ff fe 	. . . 
	ld c,h			;becd	4c 	L 
	jp m,0f6f0h		;bece	fa f0 f6 	. . . 
	nop			;bed1	00 	. 
	ret m			;bed2	f8 	. 
	jp pe,000efh		;bed3	ea ef 00 	. . . 
	jp po,000efh		;bed6	e2 ef 00 	. . . 
	and 0f9h		;bed9	e6 f9 	. . 
	push af			;bedb	f5 	. 
	di			;bedc	f3 	. 
	jp po,0ee00h		;bedd	e2 00 ee 	. . . 
	di			;bee0	f3 	. 
	defb 0fdh,001h,0feh	;illegal sequence		;bee1	fd 01 fe 	. . . 
	nop			;bee4	00 	. 
	push hl			;bee5	e5 	. 
	ret p			;bee6	f0 	. 
	nop			;bee7	00 	. 
	defb 0fdh,001h,0ffh	;illegal sequence		;bee8	fd 01 ff 	. . . 
	rst 38h			;beeb	ff 	. 
	defb 0fdh,014h,000h	;illegal sequence		;beec	fd 14 00 	. . . 
	cp 00ch		;beef	fe 0c 	. . 
	nop			;bef1	00 	. 
	ret pe			;bef2	e8 	. 
	jp po,0e6eeh		;bef3	e2 ee e6 	. . . 
	nop			;bef6	00 	. 
	ret p			;bef7	f0 	. 
	rst 30h			;bef8	f7 	. 
	and 0f3h		;bef9	e6 f3 	. . 
	nop			;befb	00 	. 
	pop af			;befc	f1 	. 
	defb 0edh;next byte illegal after ed		;befd	ed 	. 
	jp po,0e6fah		;befe	e2 fa e6 	. . . 
	di			;bf01	f3 	. 
	nop			;bf02	00 	. 
	exx			;bf03	d9 	. 
	nop			;bf04	00 	. 
	cp 00ch		;bf05	fe 0c 	. . 
	defb 0fdh,014h,000h	;illegal sequence		;bf07	fd 14 00 	. . . 
	rst 38h			;bf0a	ff 	. 
	defb 0fdh,014h,000h	;illegal sequence		;bf0b	fd 14 00 	. . . 
	cp 00ch		;bf0e	fe 0c 	. . 
	nop			;bf10	00 	. 
	ret pe			;bf11	e8 	. 
	jp po,0e6eeh		;bf12	e2 ee e6 	. . . 
	nop			;bf15	00 	. 
	ret p			;bf16	f0 	. 
	rst 30h			;bf17	f7 	. 
	and 0f3h		;bf18	e6 f3 	. . 
	nop			;bf1a	00 	. 
	pop af			;bf1b	f1 	. 
	defb 0edh;next byte illegal after ed		;bf1c	ed 	. 
	jp po,0e6fah		;bf1d	e2 fa e6 	. . . 
	di			;bf20	f3 	. 
	nop			;bf21	00 	. 
	jp c,0fe00h		;bf22	da 00 fe 	. . . 
	inc c			;bf25	0c 	. 
	defb 0fdh,014h,000h	;illegal sequence		;bf26	fd 14 00 	. . . 
	rst 38h			;bf29	ff 	. 
	defb 0fdh,00bh,000h	;illegal sequence		;bf2a	fd 0b 00 	. . . 
	cp 015h		;bf2d	fe 15 	. . 
	nop			;bf2f	00 	. 
	ret pe			;bf30	e8 	. 
	jp po,0e6eeh		;bf31	e2 ee e6 	. . . 
	nop			;bf34	00 	. 
	ret p			;bf35	f0 	. 
	rst 30h			;bf36	f7 	. 
	and 0f3h		;bf37	e6 f3 	. . 
	nop			;bf39	00 	. 
	cp 015h		;bf3a	fe 15 	. . 
	defb 0fdh,00bh,000h	;illegal sequence		;bf3c	fd 0b 00 	. . . 
	rst 38h			;bf3f	ff 	. 
	ld hl,(0fe2bh)		;bf40	2a 2b fe 	* + . 
	ld e,038h		;bf43	1e 38 	. 8 
	add hl,sp			;bf45	39 	9 
	rst 38h			;bf46	ff 	. 
	jr nz,$+35		;bf47	20 21 	  ! 
	cp 01eh		;bf49	fe 1e 	. . 
	ld (0ff23h),hl		;bf4b	22 23 ff 	" # . 
	jr $+27		;bf4e	18 19 	. . 
	cp 01eh		;bf50	fe 1e 	. . 
	ld a,(de)			;bf52	1a 	. 
	dec de			;bf53	1b 	. 
	rst 38h			;bf54	ff 	. 
	inc l			;bf55	2c 	, 
	dec l			;bf56	2d 	- 
	cp 01eh		;bf57	fe 1e 	. . 
	inc h			;bf59	24 	$ 
	dec h			;bf5a	25 	% 
	rst 38h			;bf5b	ff 	. 
	nop			;bf5c	00 	. 
	nop			;bf5d	00 	. 
	cp 01eh		;bf5e	fe 1e 	. . 
	nop			;bf60	00 	. 
	nop			;bf61	00 	. 
	rst 38h			;bf62	ff 	. 
	ld b,l			;bf63	45 	E 
	ld b,(hl)			;bf64	46 	F 
	ld b,a			;bf65	47 	G 
	rst 38h			;bf66	ff 	. 
	ld a,e			;bf67	7b 	{ 
	cp a			;bf68	bf 	. 
	sbc a,e			;bf69	9b 	. 
	cp a			;bf6a	bf 	. 
	and a			;bf6b	a7 	. 
	cp a			;bf6c	bf 	. 
	or e			;bf6d	b3 	. 
	cp a			;bf6e	bf 	. 
	cp a			;bf6f	bf 	. 
	cp a			;bf70	bf 	. 
	res 7,a		;bf71	cb bf 	. . 
	rst 10h			;bf73	d7 	. 
	cp a			;bf74	bf 	. 
	ex (sp),hl			;bf75	e3 	. 
	cp a			;bf76	bf 	. 
	rst 28h			;bf77	ef 	. 
	cp a			;bf78	bf 	. 
	ei			;bf79	fb 	. 
	cp a			;bf7a	bf 	. 
	nop			;bf7b	00 	. 
	inc e			;bf7c	1c 	. 
	adc a,h			;bf7d	8c 	. 
	sub b			;bf7e	90 	. 
	add a,b			;bf7f	80 	. 
	ret p			;bf80	f0 	. 
	ret p			;bf81	f0 	. 
	and b			;bf82	a0 	. 
	and b			;bf83	a0 	. 
	add a,b			;bf84	80 	. 
	jp z,0c0c0h		;bf85	ca c0 c0 	. . . 
	ret nz			;bf88	c0 	. 
	add a,b			;bf89	80 	. 
	ret po			;bf8a	e0 	. 
	nop			;bf8b	00 	. 
	nop			;bf8c	00 	. 
	nop			;bf8d	00 	. 
	nop			;bf8e	00 	. 
	nop			;bf8f	00 	. 
	nop			;bf90	00 	. 
	nop			;bf91	00 	. 
	nop			;bf92	00 	. 
	nop			;bf93	00 	. 
	nop			;bf94	00 	. 
	nop			;bf95	00 	. 
	ret p			;bf96	f0 	. 
	ret p			;bf97	f0 	. 
	ret p			;bf98	f0 	. 
	ret p			;bf99	f0 	. 
	ret p			;bf9a	f0 	. 
	nop			;bf9b	00 	. 
	inc d			;bf9c	14 	. 
	add a,h			;bf9d	84 	. 
	sub b			;bf9e	90 	. 
	add a,b			;bf9f	80 	. 
	ret p			;bfa0	f0 	. 
	ret p			;bfa1	f0 	. 
	and b			;bfa2	a0 	. 
	and b			;bfa3	a0 	. 
	add a,b			;bfa4	80 	. 
	ld b,l			;bfa5	45 	E 
	ld b,b			;bfa6	40 	@ 
	nop			;bfa7	00 	. 
	ld a,(de)			;bfa8	1a 	. 
	adc a,d			;bfa9	8a 	. 
	sub b			;bfaa	90 	. 
	add a,b			;bfab	80 	. 
	ret p			;bfac	f0 	. 
	ret p			;bfad	f0 	. 
	and b			;bfae	a0 	. 
	and b			;bfaf	a0 	. 
	add a,b			;bfb0	80 	. 
	jp z,000a0h		;bfb1	ca a0 00 	. . . 
	dec e			;bfb4	1d 	. 
	adc a,l			;bfb5	8d 	. 
	sub b			;bfb6	90 	. 
	add a,b			;bfb7	80 	. 
	ret p			;bfb8	f0 	. 
	ret p			;bfb9	f0 	. 
	and b			;bfba	a0 	. 
	and b			;bfbb	a0 	. 
	add a,b			;bfbc	80 	. 
	pop de			;bfbd	d1 	. 
	ret nc			;bfbe	d0 	. 
	nop			;bfbf	00 	. 
	dec d			;bfc0	15 	. 
	add a,l			;bfc1	85 	. 
	sub b			;bfc2	90 	. 
	add a,b			;bfc3	80 	. 
	ret p			;bfc4	f0 	. 
	ret p			;bfc5	f0 	. 
	and b			;bfc6	a0 	. 
	and b			;bfc7	a0 	. 
	add a,b			;bfc8	80 	. 
	and l			;bfc9	a5 	. 
	ld d,b			;bfca	50 	P 
	nop			;bfcb	00 	. 
	dec de			;bfcc	1b 	. 
	adc a,e			;bfcd	8b 	. 
	sub b			;bfce	90 	. 
	add a,b			;bfcf	80 	. 
	ret p			;bfd0	f0 	. 
	ret p			;bfd1	f0 	. 
	and b			;bfd2	a0 	. 
	and b			;bfd3	a0 	. 
	add a,b			;bfd4	80 	. 
	sbc a,e			;bfd5	9b 	. 
	or b			;bfd6	b0 	. 
	nop			;bfd7	00 	. 
	inc e			;bfd8	1c 	. 
	adc a,h			;bfd9	8c 	. 
	sub b			;bfda	90 	. 
	add a,b			;bfdb	80 	. 
	ret p			;bfdc	f0 	. 
	ret p			;bfdd	f0 	. 
	and b			;bfde	a0 	. 
	and b			;bfdf	a0 	. 
	add a,b			;bfe0	80 	. 
	inc a			;bfe1	3c 	< 
	ret nz			;bfe2	c0 	. 
	nop			;bfe3	00 	. 
	rla			;bfe4	17 	. 
	add a,a			;bfe5	87 	. 
	sub b			;bfe6	90 	. 
	add a,b			;bfe7	80 	. 
	ret p			;bfe8	f0 	. 
	ret p			;bfe9	f0 	. 
	and b			;bfea	a0 	. 
	and b			;bfeb	a0 	. 
	add a,b			;bfec	80 	. 
	ld (hl),h			;bfed	74 	t 
	ld (hl),b			;bfee	70 	p 
	nop			;bfef	00 	. 
	inc d			;bff0	14 	. 
	add a,h			;bff1	84 	. 
	sub b			;bff2	90 	. 
	add a,b			;bff3	80 	. 
	ret p			;bff4	f0 	. 
	ret p			;bff5	f0 	. 
	and b			;bff6	a0 	. 
	and b			;bff7	a0 	. 
	add a,b			;bff8	80 	. 
	or h			;bff9	b4 	. 
	ld b,b			;bffa	40 	@ 
	nop			;bffb	00 	. 
	inc e			;bffc	1c 	. 
	adc a,h			;bffd	8c 	. 
	sub b			;bffe	90 	. 
	add a,b			;bfff	80 	. 
	ret p			;c000	f0 	. 
	ret p			;c001	f0 	. 
	and b			;c002	a0 	. 
	and b			;c003	a0 	. 
	add a,b			;c004	80 	. 
	call c,01bc0h		;c005	dc c0 1b 	. . . 
	ret nz			;c008	c0 	. 
	ld (035c0h),hl		;c009	22 c0 35 	" . 5 
	ret nz			;c00c	c0 	. 
	ld c,d			;c00d	4a 	J 
	ret nz			;c00e	c0 	. 
	ld h,a			;c00f	67 	g 
	ret nz			;c010	c0 	. 
	ld a,h			;c011	7c 	| 
	ret nz			;c012	c0 	. 
	sub c			;c013	91 	. 
	ret nz			;c014	c0 	. 
	sbc a,b			;c015	98 	. 
	ret nz			;c016	c0 	. 
	xor l			;c017	ad 	. 
	ret nz			;c018	c0 	. 
	jp nz,006c0h		;c019	c2 c0 06 	. . . 
	ld c,b			;c01c	48 	H 
	ld e,b			;c01d	58 	X 
	ld l,b			;c01e	68 	h 
	ld a,b			;c01f	78 	x 
	adc a,b			;c020	88 	. 
	sbc a,b			;c021	98 	. 
	ld (de),a			;c022	12 	. 
	ld c,b			;c023	48 	H 
	ld e,b			;c024	58 	X 
	ld d,a			;c025	57 	W 
	ld d,(hl)			;c026	56 	V 
	ld d,l			;c027	55 	U 
	ld h,l			;c028	65 	e 
	ld h,h			;c029	64 	d 
	ld (hl),h			;c02a	74 	t 
	ld (hl),e			;c02b	73 	s 
	ld (hl),d			;c02c	72 	r 
	add a,d			;c02d	82 	. 
	sub d			;c02e	92 	. 
	sub e			;c02f	93 	. 
	sub h			;c030	94 	. 
	sub l			;c031	95 	. 
	sub (hl)			;c032	96 	. 
	sub a			;c033	97 	. 
	sbc a,b			;c034	98 	. 
	inc d			;c035	14 	. 
	ld c,b			;c036	48 	H 
	ld e,b			;c037	58 	X 
	ld e,c			;c038	59 	Y 
	ld e,d			;c039	5a 	Z 
	ld e,e			;c03a	5b 	[ 
	ld e,h			;c03b	5c 	\ 
	ld e,l			;c03c	5d 	] 
	ld e,(hl)			;c03d	5e 	^ 
	ld e,a			;c03e	5f 	_ 
	ld l,a			;c03f	6f 	o 
	ld a,a			;c040	7f 	 
	adc a,a			;c041	8f 	. 
	adc a,(hl)			;c042	8e 	. 
	sbc a,(hl)			;c043	9e 	. 
	sbc a,l			;c044	9d 	. 
	sbc a,h			;c045	9c 	. 
	sbc a,e			;c046	9b 	. 
	sbc a,d			;c047	9a 	. 
	sbc a,c			;c048	99 	. 
	sbc a,b			;c049	98 	. 
	inc e			;c04a	1c 	. 
	ld c,b			;c04b	48 	H 
	ld b,a			;c04c	47 	G 
	ld b,(hl)			;c04d	46 	F 
	ld b,l			;c04e	45 	E 
	ld b,h			;c04f	44 	D 
	ld d,h			;c050	54 	T 
	ld d,e			;c051	53 	S 
	ld d,d			;c052	52 	R 
	ld h,d			;c053	62 	b 
	ld (hl),d			;c054	72 	r 
	ld (hl),e			;c055	73 	s 
	ld (hl),h			;c056	74 	t 
	ld (hl),l			;c057	75 	u 
	halt			;c058	76 	v 
	ld (hl),a			;c059	77 	w 
	ld a,b			;c05a	78 	x 
	ld a,c			;c05b	79 	y 
	ld a,d			;c05c	7a 	z 
	ld a,e			;c05d	7b 	{ 
	ld a,h			;c05e	7c 	| 
	ld a,l			;c05f	7d 	} 
	adc a,l			;c060	8d 	. 
	sbc a,l			;c061	9d 	. 
	sbc a,h			;c062	9c 	. 
	sbc a,e			;c063	9b 	. 
	sbc a,d			;c064	9a 	. 
	sbc a,c			;c065	99 	. 
	sbc a,b			;c066	98 	. 
	inc d			;c067	14 	. 
	ld c,b			;c068	48 	H 
	ld c,c			;c069	49 	I 
	ld c,d			;c06a	4a 	J 
	ld c,e			;c06b	4b 	K 
	ld c,h			;c06c	4c 	L 
	ld c,l			;c06d	4d 	M 
	ld c,(hl)			;c06e	4e 	N 
	ld e,(hl)			;c06f	5e 	^ 
	ld e,a			;c070	5f 	_ 
	ld l,a			;c071	6f 	o 
	ld a,a			;c072	7f 	 
	adc a,a			;c073	8f 	. 
	adc a,(hl)			;c074	8e 	. 
	sbc a,(hl)			;c075	9e 	. 
	sbc a,l			;c076	9d 	. 
	sbc a,h			;c077	9c 	. 
	sbc a,e			;c078	9b 	. 
	sbc a,d			;c079	9a 	. 
	sbc a,c			;c07a	99 	. 
	sbc a,b			;c07b	98 	. 
	inc d			;c07c	14 	. 
	ld c,b			;c07d	48 	H 
	ld e,b			;c07e	58 	X 
	ld e,c			;c07f	59 	Y 
	ld e,d			;c080	5a 	Z 
	ld e,e			;c081	5b 	[ 
	ld e,h			;c082	5c 	\ 
	ld e,l			;c083	5d 	] 
	ld e,(hl)			;c084	5e 	^ 
	ld e,a			;c085	5f 	_ 
	ld l,a			;c086	6f 	o 
	ld a,a			;c087	7f 	 
	adc a,a			;c088	8f 	. 
	adc a,(hl)			;c089	8e 	. 
	sbc a,(hl)			;c08a	9e 	. 
	sbc a,l			;c08b	9d 	. 
	sbc a,h			;c08c	9c 	. 
	sbc a,e			;c08d	9b 	. 
	sbc a,d			;c08e	9a 	. 
	sbc a,c			;c08f	99 	. 
	sbc a,b			;c090	98 	. 
	ld b,048h		;c091	06 48 	. H 
	ld e,b			;c093	58 	X 
	ld l,b			;c094	68 	h 
	ld a,b			;c095	78 	x 
	adc a,b			;c096	88 	. 
	sbc a,b			;c097	98 	. 
	inc d			;c098	14 	. 
	ld c,b			;c099	48 	H 
	ld e,b			;c09a	58 	X 
	ld e,c			;c09b	59 	Y 
	ld e,d			;c09c	5a 	Z 
	ld e,e			;c09d	5b 	[ 
	ld e,h			;c09e	5c 	\ 
	ld e,l			;c09f	5d 	] 
	ld e,(hl)			;c0a0	5e 	^ 
	ld l,(hl)			;c0a1	6e 	n 
	ld l,a			;c0a2	6f 	o 
	ld a,a			;c0a3	7f 	 
	adc a,a			;c0a4	8f 	. 
	adc a,(hl)			;c0a5	8e 	. 
	sbc a,(hl)			;c0a6	9e 	. 
	sbc a,l			;c0a7	9d 	. 
	sbc a,h			;c0a8	9c 	. 
	sbc a,e			;c0a9	9b 	. 
	sbc a,d			;c0aa	9a 	. 
	sbc a,c			;c0ab	99 	. 
	sbc a,b			;c0ac	98 	. 
	inc d			;c0ad	14 	. 
	ld c,b			;c0ae	48 	H 
	ld e,b			;c0af	58 	X 
	ld e,c			;c0b0	59 	Y 
	ld e,d			;c0b1	5a 	Z 
	ld e,e			;c0b2	5b 	[ 
	ld e,h			;c0b3	5c 	\ 
	ld e,l			;c0b4	5d 	] 
	ld e,(hl)			;c0b5	5e 	^ 
	ld e,a			;c0b6	5f 	_ 
	ld l,a			;c0b7	6f 	o 
	ld a,a			;c0b8	7f 	 
	adc a,a			;c0b9	8f 	. 
	adc a,(hl)			;c0ba	8e 	. 
	sbc a,(hl)			;c0bb	9e 	. 
	sbc a,l			;c0bc	9d 	. 
	sbc a,h			;c0bd	9c 	. 
	sbc a,e			;c0be	9b 	. 
	sbc a,d			;c0bf	9a 	. 
	sbc a,c			;c0c0	99 	. 
	sbc a,b			;c0c1	98 	. 
	ld (de),a			;c0c2	12 	. 
	ld c,b			;c0c3	48 	H 
	ld c,c			;c0c4	49 	I 
	ld e,c			;c0c5	59 	Y 
	ld e,d			;c0c6	5a 	Z 
	ld l,d			;c0c7	6a 	j 
	ld l,e			;c0c8	6b 	k 
	ld a,e			;c0c9	7b 	{ 
	ld a,h			;c0ca	7c 	| 
	adc a,h			;c0cb	8c 	. 
	adc a,l			;c0cc	8d 	. 
	adc a,(hl)			;c0cd	8e 	. 
	sbc a,(hl)			;c0ce	9e 	. 
	sbc a,l			;c0cf	9d 	. 
	sbc a,h			;c0d0	9c 	. 
	sbc a,e			;c0d1	9b 	. 
	sbc a,d			;c0d2	9a 	. 
	sbc a,c			;c0d3	99 	. 
	sbc a,b			;c0d4	98 	. 
	nop			;c0d5	00 	. 
	nop			;c0d6	00 	. 
	nop			;c0d7	00 	. 
	nop			;c0d8	00 	. 
	ret nz			;c0d9	c0 	. 
	jp 00400h		;c0da	c3 00 04 	. . . 
	nop			;c0dd	00 	. 
	ret po			;c0de	e0 	. 
	jp 03401h		;c0df	c3 01 34 	. . 4 
	jp nz,0c3c0h		;c0e2	c2 c0 c3 	. . . 
	ld bc,0c238h		;c0e5	01 38 c2 	. 8 . 
	ret po			;c0e8	e0 	. 
	jp 03c02h		;c0e9	c3 02 3c 	. . < 
	jp nz,0c3c0h		;c0ec	c2 c0 c3 	. . . 
	ld (bc),a			;c0ef	02 	. 
	ld b,b			;c0f0	40 	@ 
	jp nz,0c3e0h		;c0f1	c2 e0 c3 	. . . 
	inc bc			;c0f4	03 	. 
	ld b,h			;c0f5	44 	D 
	jp nz,0c3c0h		;c0f6	c2 c0 c3 	. . . 
	inc bc			;c0f9	03 	. 
	ld c,b			;c0fa	48 	H 
	jp nz,0c3e0h		;c0fb	c2 e0 c3 	. . . 
	inc b			;c0fe	04 	. 
	ld c,h			;c0ff	4c 	L 
	jp nz,0c3c0h		;c100	c2 c0 c3 	. . . 
	inc b			;c103	04 	. 
	ld d,b			;c104	50 	P 
	jp nz,0c3e0h		;c105	c2 e0 c3 	. . . 
	dec b			;c108	05 	. 
	ld d,h			;c109	54 	T 
	jp nz,0c3c0h		;c10a	c2 c0 c3 	. . . 
	dec b			;c10d	05 	. 
	ld e,b			;c10e	58 	X 
	jp nz,0c3e0h		;c10f	c2 e0 c3 	. . . 
	nop			;c112	00 	. 
	jr nc,$+2		;c113	30 00 	0 . 
	add a,b			;c115	80 	. 
	jp 03400h		;c116	c3 00 34 	. . 4 
	nop			;c119	00 	. 
	and b			;c11a	a0 	. 
	jp 05c01h		;c11b	c3 01 5c 	. . \ 
	jp nz,0c380h		;c11e	c2 80 c3 	. . . 
	ld bc,0c260h		;c121	01 60 c2 	. ` . 
	and b			;c124	a0 	. 
	jp 06402h		;c125	c3 02 64 	. . d 
	jp nz,0c380h		;c128	c2 80 c3 	. . . 
	ld (bc),a			;c12b	02 	. 
	ld l,b			;c12c	68 	h 
	jp nz,0c3a0h		;c12d	c2 a0 c3 	. . . 
	inc bc			;c130	03 	. 
	ld l,h			;c131	6c 	l 
	jp nz,0c380h		;c132	c2 80 c3 	. . . 
	inc bc			;c135	03 	. 
	ld (hl),b			;c136	70 	p 
	jp nz,0c3a0h		;c137	c2 a0 c3 	. . . 
	inc b			;c13a	04 	. 
	ld (hl),h			;c13b	74 	t 
	jp nz,0c380h		;c13c	c2 80 c3 	. . . 
	inc b			;c13f	04 	. 
	ld a,b			;c140	78 	x 
	jp nz,0c3a0h		;c141	c2 a0 c3 	. . . 
	dec b			;c144	05 	. 
	ld a,h			;c145	7c 	| 
	jp nz,0c380h		;c146	c2 80 c3 	. . . 
	dec b			;c149	05 	. 
	add a,b			;c14a	80 	. 
	jp nz,0c3a0h		;c14b	c2 a0 c3 	. . . 
	nop			;c14e	00 	. 
	ret po			;c14f	e0 	. 
	nop			;c150	00 	. 
	nop			;c151	00 	. 
	call nz,0e400h		;c152	c4 00 e4 	. . . 
	nop			;c155	00 	. 
	jr nz,$-58		;c156	20 c4 	  . 
	ld bc,0c298h		;c158	01 98 c2 	. . . 
	nop			;c15b	00 	. 
	call nz,09c01h		;c15c	c4 01 9c 	. . . 
	jp nz,0c420h		;c15f	c2 20 c4 	.   . 
	nop			;c162	00 	. 
	or b			;c163	b0 	. 
	nop			;c164	00 	. 
	and b			;c165	a0 	. 
	jp nz,0b000h		;c166	c2 00 b0 	. . . 
	nop			;c169	00 	. 
	ret nz			;c16a	c0 	. 
	jp nz,0b000h		;c16b	c2 00 b0 	. . . 
	nop			;c16e	00 	. 
	ret po			;c16f	e0 	. 
	jp nz,0b000h		;c170	c2 00 b0 	. . . 
	nop			;c173	00 	. 
	nop			;c174	00 	. 
	jp 0b000h		;c175	c3 00 b0 	. . . 
	nop			;c178	00 	. 
	ld b,b			;c179	40 	@ 
	jp 0b000h		;c17a	c3 00 b0 	. . . 
	nop			;c17d	00 	. 
	ld h,b			;c17e	60 	` 
	jp 0b000h		;c17f	c3 00 b0 	. . . 
	nop			;c182	00 	. 
	nop			;c183	00 	. 
	jp 08401h		;c184	c3 01 84 	. . . 
	jp nz,0c2a0h		;c187	c2 a0 c2 	. . . 
	ld bc,0c284h		;c18a	01 84 c2 	. . . 
	ret nz			;c18d	c0 	. 
	jp nz,08401h		;c18e	c2 01 84 	. . . 
	jp nz,0c2e0h		;c191	c2 e0 c2 	. . . 
	ld bc,0c284h		;c194	01 84 c2 	. . . 
	nop			;c197	00 	. 
	jp 08401h		;c198	c3 01 84 	. . . 
	jp nz,0c340h		;c19b	c2 40 c3 	. @ . 
	ld bc,0c284h		;c19e	01 84 c2 	. . . 
	ld h,b			;c1a1	60 	` 
	jp 08401h		;c1a2	c3 01 84 	. . . 
	jp nz,0c300h		;c1a5	c2 00 c3 	. . . 
	ld (bc),a			;c1a8	02 	. 
	adc a,b			;c1a9	88 	. 
	jp nz,0c2a0h		;c1aa	c2 a0 c2 	. . . 
	ld (bc),a			;c1ad	02 	. 
	adc a,b			;c1ae	88 	. 
	jp nz,0c2c0h		;c1af	c2 c0 c2 	. . . 
	ld (bc),a			;c1b2	02 	. 
	adc a,b			;c1b3	88 	. 
	jp nz,0c2e0h		;c1b4	c2 e0 c2 	. . . 
	ld (bc),a			;c1b7	02 	. 
	adc a,b			;c1b8	88 	. 
	jp nz,0c300h		;c1b9	c2 00 c3 	. . . 
	ld (bc),a			;c1bc	02 	. 
	adc a,b			;c1bd	88 	. 
	jp nz,0c340h		;c1be	c2 40 c3 	. @ . 
	ld (bc),a			;c1c1	02 	. 
	adc a,b			;c1c2	88 	. 
	jp nz,0c360h		;c1c3	c2 60 c3 	. ` . 
	ld (bc),a			;c1c6	02 	. 
	adc a,b			;c1c7	88 	. 
	jp nz,0c300h		;c1c8	c2 00 c3 	. . . 
	inc bc			;c1cb	03 	. 
	adc a,h			;c1cc	8c 	. 
	jp nz,0c2a0h		;c1cd	c2 a0 c2 	. . . 
	inc bc			;c1d0	03 	. 
	adc a,h			;c1d1	8c 	. 
	jp nz,0c2c0h		;c1d2	c2 c0 c2 	. . . 
	inc bc			;c1d5	03 	. 
	adc a,h			;c1d6	8c 	. 
	jp nz,0c2e0h		;c1d7	c2 e0 c2 	. . . 
	inc bc			;c1da	03 	. 
	adc a,h			;c1db	8c 	. 
	jp nz,0c300h		;c1dc	c2 00 c3 	. . . 
	inc bc			;c1df	03 	. 
	adc a,h			;c1e0	8c 	. 
	jp nz,0c340h		;c1e1	c2 40 c3 	. @ . 
	inc bc			;c1e4	03 	. 
	adc a,h			;c1e5	8c 	. 
	jp nz,0c360h		;c1e6	c2 60 c3 	. ` . 
	inc bc			;c1e9	03 	. 
	adc a,h			;c1ea	8c 	. 
	jp nz,0c300h		;c1eb	c2 00 c3 	. . . 
	inc b			;c1ee	04 	. 
	sub b			;c1ef	90 	. 
	jp nz,0c2a0h		;c1f0	c2 a0 c2 	. . . 
	inc b			;c1f3	04 	. 
	sub b			;c1f4	90 	. 
	jp nz,0c2c0h		;c1f5	c2 c0 c2 	. . . 
	inc b			;c1f8	04 	. 
	sub b			;c1f9	90 	. 
	jp nz,0c2e0h		;c1fa	c2 e0 c2 	. . . 
	inc b			;c1fd	04 	. 
	sub b			;c1fe	90 	. 
	jp nz,0c300h		;c1ff	c2 00 c3 	. . . 
	inc b			;c202	04 	. 
	sub b			;c203	90 	. 
	jp nz,0c340h		;c204	c2 40 c3 	. @ . 
	inc b			;c207	04 	. 
	sub b			;c208	90 	. 
	jp nz,0c360h		;c209	c2 60 c3 	. ` . 
	inc b			;c20c	04 	. 
	sub b			;c20d	90 	. 
	jp nz,0c300h		;c20e	c2 00 c3 	. . . 
	dec b			;c211	05 	. 
	sub h			;c212	94 	. 
	jp nz,0c2a0h		;c213	c2 a0 c2 	. . . 
	dec b			;c216	05 	. 
	sub h			;c217	94 	. 
	jp nz,0c2c0h		;c218	c2 c0 c2 	. . . 
	dec b			;c21b	05 	. 
	sub h			;c21c	94 	. 
	jp nz,0c2e0h		;c21d	c2 e0 c2 	. . . 
	dec b			;c220	05 	. 
	sub h			;c221	94 	. 
	jp nz,0c300h		;c222	c2 00 c3 	. . . 
	dec b			;c225	05 	. 
	sub h			;c226	94 	. 
	jp nz,0c340h		;c227	c2 40 c3 	. @ . 
	dec b			;c22a	05 	. 
	sub h			;c22b	94 	. 
	jp nz,0c360h		;c22c	c2 60 c3 	. ` . 
	dec b			;c22f	05 	. 
	sub h			;c230	94 	. 
	jp nz,0c300h		;c231	c2 00 c3 	. . . 
	ld a,(bc)			;c234	0a 	. 
	dec bc			;c235	0b 	. 
	ex af,af'			;c236	08 	. 
	add hl,bc			;c237	09 	. 
	ld c,00fh		;c238	0e 0f 	. . 
	inc c			;c23a	0c 	. 
	dec c			;c23b	0d 	. 
	ld de,01013h		;c23c	11 13 10 	. . . 
	ld (de),a			;c23f	12 	. 
	dec d			;c240	15 	. 
	rla			;c241	17 	. 
	inc d			;c242	14 	. 
	ld d,018h		;c243	16 18 	. . 
	ld a,(de)			;c245	1a 	. 
	add hl,de			;c246	19 	. 
	dec de			;c247	1b 	. 
	inc e			;c248	1c 	. 
	ld e,01dh		;c249	1e 1d 	. . 
	rra			;c24b	1f 	. 
	inc hl			;c24c	23 	# 
	ld hl,02022h		;c24d	21 22 20 	! "   
	daa			;c250	27 	' 
	dec h			;c251	25 	% 
	ld h,024h		;c252	26 24 	& $ 
	ld hl,(02b28h)		;c254	2a 28 2b 	* ( + 
	add hl,hl			;c257	29 	) 
	ld l,02ch		;c258	2e 2c 	. , 
	cpl			;c25a	2f 	/ 
	dec l			;c25b	2d 	- 
	ld a,(0383bh)		;c25c	3a 3b 38 	: ; 8 
	add hl,sp			;c25f	39 	9 
	ld a,03fh		;c260	3e 3f 	> ? 
	inc a			;c262	3c 	< 
	dec a			;c263	3d 	= 
	ld b,c			;c264	41 	A 
	ld b,e			;c265	43 	C 
	ld b,b			;c266	40 	@ 
	ld b,d			;c267	42 	B 
	ld b,l			;c268	45 	E 
	ld b,a			;c269	47 	G 
	ld b,h			;c26a	44 	D 
	ld b,(hl)			;c26b	46 	F 
	ld c,b			;c26c	48 	H 
	ld c,d			;c26d	4a 	J 
	ld c,c			;c26e	49 	I 
	ld c,e			;c26f	4b 	K 
	ld c,h			;c270	4c 	L 
	ld c,(hl)			;c271	4e 	N 
	ld c,l			;c272	4d 	M 
	ld c,a			;c273	4f 	O 
	ld d,e			;c274	53 	S 
	ld d,c			;c275	51 	Q 
	ld d,d			;c276	52 	R 
	ld d,b			;c277	50 	P 
	ld d,a			;c278	57 	W 
	ld d,l			;c279	55 	U 
	ld d,(hl)			;c27a	56 	V 
	ld d,h			;c27b	54 	T 
	ld e,d			;c27c	5a 	Z 
	ld e,b			;c27d	58 	X 
	ld e,e			;c27e	5b 	[ 
	ld e,c			;c27f	59 	Y 
	ld e,(hl)			;c280	5e 	^ 
	ld e,h			;c281	5c 	\ 
	ld e,a			;c282	5f 	_ 
	ld e,l			;c283	5d 	] 
	or d			;c284	b2 	. 
	or e			;c285	b3 	. 
	or b			;c286	b0 	. 
	or c			;c287	b1 	. 
	or c			;c288	b1 	. 
	or e			;c289	b3 	. 
	or b			;c28a	b0 	. 
	or d			;c28b	b2 	. 
	or b			;c28c	b0 	. 
	or d			;c28d	b2 	. 
	or c			;c28e	b1 	. 
	or e			;c28f	b3 	. 
	or e			;c290	b3 	. 
	or c			;c291	b1 	. 
	or d			;c292	b2 	. 
	or b			;c293	b0 	. 
	or d			;c294	b2 	. 
	or b			;c295	b0 	. 
	or e			;c296	b3 	. 
	or c			;c297	b1 	. 
	jp pe,0e8ebh		;c298	ea eb e8 	. . . 
	jp (hl)			;c29b	e9 	. 
	xor 0efh		;c29c	ee ef 	. . 
	call pe,000edh		;c29e	ec ed 00 	. . . 
	nop			;c2a1	00 	. 
	rra			;c2a2	1f 	. 
	ccf			;c2a3	3f 	? 
	daa			;c2a4	27 	' 
	inc bc			;c2a5	03 	. 
	ld bc,00301h		;c2a6	01 01 03 	. . . 
	rlca			;c2a9	07 	. 
	rlca			;c2aa	07 	. 
	inc bc			;c2ab	03 	. 
	dec b			;c2ac	05 	. 
	ld b,000h		;c2ad	06 00 	. . 
	nop			;c2af	00 	. 
	nop			;c2b0	00 	. 
	nop			;c2b1	00 	. 
	ret po			;c2b2	e0 	. 
	ret po			;c2b3	e0 	. 
	ret p			;c2b4	f0 	. 
	ret c			;c2b5	d8 	. 
	ret c			;c2b6	d8 	. 
	ret p			;c2b7	f0 	. 
	ret nz			;c2b8	c0 	. 
	ret m			;c2b9	f8 	. 
	ret m			;c2ba	f8 	. 
	ret nz			;c2bb	c0 	. 
	ret po			;c2bc	e0 	. 
	ret m			;c2bd	f8 	. 
	nop			;c2be	00 	. 
	nop			;c2bf	00 	. 
	nop			;c2c0	00 	. 
	nop			;c2c1	00 	. 
	rlca			;c2c2	07 	. 
	rra			;c2c3	1f 	. 
	ccf			;c2c4	3f 	? 
	inc hl			;c2c5	23 	# 
	ld bc,01f01h		;c2c6	01 01 1f 	. . . 
	rlca			;c2c9	07 	. 
	inc bc			;c2ca	03 	. 
	ccf			;c2cb	3f 	? 
	ccf			;c2cc	3f 	? 
	jr nz,$+2		;c2cd	20 00 	  . 
	nop			;c2cf	00 	. 
	nop			;c2d0	00 	. 
	nop			;c2d1	00 	. 
	ret po			;c2d2	e0 	. 
	ret po			;c2d3	e0 	. 
	ret p			;c2d4	f0 	. 
	ret c			;c2d5	d8 	. 
	ret c			;c2d6	d8 	. 
	ret p			;c2d7	f0 	. 
	ret nz			;c2d8	c0 	. 
	call m,0e0fch		;c2d9	fc fc e0 	. . . 
	ret p			;c2dc	f0 	. 
	ld a,h			;c2dd	7c 	| 
	nop			;c2de	00 	. 
	nop			;c2df	00 	. 
	nop			;c2e0	00 	. 
	nop			;c2e1	00 	. 
	rra			;c2e2	1f 	. 
	ccf			;c2e3	3f 	? 
	daa			;c2e4	27 	' 
	inc bc			;c2e5	03 	. 
	ld bc,00301h		;c2e6	01 01 03 	. . . 
	rlca			;c2e9	07 	. 
	rlca			;c2ea	07 	. 
	inc bc			;c2eb	03 	. 
	dec b			;c2ec	05 	. 
	ld b,000h		;c2ed	06 00 	. . 
	nop			;c2ef	00 	. 
	nop			;c2f0	00 	. 
	nop			;c2f1	00 	. 
	ret po			;c2f2	e0 	. 
	ret po			;c2f3	e0 	. 
	ret p			;c2f4	f0 	. 
	ret c			;c2f5	d8 	. 
	ret c			;c2f6	d8 	. 
	ret p			;c2f7	f0 	. 
	call nz,0fcfch		;c2f8	c4 fc fc 	. . . 
	ret nz			;c2fb	c0 	. 
	ret po			;c2fc	e0 	. 
	ret m			;c2fd	f8 	. 
	nop			;c2fe	00 	. 
	nop			;c2ff	00 	. 
	nop			;c300	00 	. 
	nop			;c301	00 	. 
	rlca			;c302	07 	. 
	rra			;c303	1f 	. 
	ccf			;c304	3f 	? 
	inc hl			;c305	23 	# 
	ld bc,00101h		;c306	01 01 01 	. . . 
	inc bc			;c309	03 	. 
	inc bc			;c30a	03 	. 
	ccf			;c30b	3f 	? 
	ccf			;c30c	3f 	? 
	jr nz,$+2		;c30d	20 00 	  . 
	nop			;c30f	00 	. 
	nop			;c310	00 	. 
	nop			;c311	00 	. 
	ret po			;c312	e0 	. 
	ret po			;c313	e0 	. 
	ret p			;c314	f0 	. 
	ret c			;c315	d8 	. 
	ret c			;c316	d8 	. 
	ret p			;c317	f0 	. 
	call nz,0fcfch		;c318	c4 fc fc 	. . . 
	ret nz			;c31b	c0 	. 
	ret p			;c31c	f0 	. 
	ld a,h			;c31d	7c 	| 
	nop			;c31e	00 	. 
	nop			;c31f	00 	. 
	nop			;c320	00 	. 
	nop			;c321	00 	. 
	inc bc			;c322	03 	. 
	rlca			;c323	07 	. 
	add hl,bc			;c324	09 	. 
	dec c			;c325	0d 	. 
	rlca			;c326	07 	. 
	inc bc			;c327	03 	. 
	rlca			;c328	07 	. 
	ld c,01fh		;c329	0e 1f 	. . 
	rra			;c32b	1f 	. 
	ld (de),a			;c32c	12 	. 
	rra			;c32d	1f 	. 
	nop			;c32e	00 	. 
	nop			;c32f	00 	. 
	nop			;c330	00 	. 
	nop			;c331	00 	. 
	ret nz			;c332	c0 	. 
	ret po			;c333	e0 	. 
	sub b			;c334	90 	. 
	or b			;c335	b0 	. 
	ret po			;c336	e0 	. 
	ret z			;c337	c8 	. 
	ret m			;c338	f8 	. 
	jr c,$-62		;c339	38 c0 	8 . 
	ret nz			;c33b	c0 	. 
	nop			;c33c	00 	. 
	add a,b			;c33d	80 	. 
	nop			;c33e	00 	. 
	nop			;c33f	00 	. 
	nop			;c340	00 	. 
	nop			;c341	00 	. 
	inc bc			;c342	03 	. 
	rlca			;c343	07 	. 
	add hl,bc			;c344	09 	. 
	dec c			;c345	0d 	. 
	rlca			;c346	07 	. 
	inc bc			;c347	03 	. 
	inc bc			;c348	03 	. 
	ld b,00fh		;c349	06 0f 	. . 
	rrca			;c34b	0f 	. 
	rrca			;c34c	0f 	. 
	ld bc,00000h		;c34d	01 00 00 	. . . 
	nop			;c350	00 	. 
	nop			;c351	00 	. 
	ret nz			;c352	c0 	. 
	ret po			;c353	e0 	. 
	sub b			;c354	90 	. 
	or b			;c355	b0 	. 
	ret po			;c356	e0 	. 
	ret z			;c357	c8 	. 
	ret m			;c358	f8 	. 
	jr c,$-62		;c359	38 c0 	8 . 
	ret nz			;c35b	c0 	. 
	nop			;c35c	00 	. 
	ret nz			;c35d	c0 	. 
	nop			;c35e	00 	. 
	nop			;c35f	00 	. 
	nop			;c360	00 	. 
	nop			;c361	00 	. 
	inc bc			;c362	03 	. 
	rlca			;c363	07 	. 
	add hl,bc			;c364	09 	. 
	dec c			;c365	0d 	. 
	rlca			;c366	07 	. 
	inc bc			;c367	03 	. 
	rlca			;c368	07 	. 
	ld c,01fh		;c369	0e 1f 	. . 
	rra			;c36b	1f 	. 
	inc de			;c36c	13 	. 
	inc e			;c36d	1c 	. 
	nop			;c36e	00 	. 
	nop			;c36f	00 	. 
	nop			;c370	00 	. 
	nop			;c371	00 	. 
	ret nz			;c372	c0 	. 
	ret po			;c373	e0 	. 
	sub b			;c374	90 	. 
	or b			;c375	b0 	. 
	ret po			;c376	e0 	. 
	ret z			;c377	c8 	. 
	ret m			;c378	f8 	. 
	jr c,$-126		;c379	38 80 	8 . 
	add a,b			;c37b	80 	. 
	add a,b			;c37c	80 	. 
	nop			;c37d	00 	. 
	nop			;c37e	00 	. 
	nop			;c37f	00 	. 
	nop			;c380	00 	. 
	nop			;c381	00 	. 
	rlca			;c382	07 	. 
	rrca			;c383	0f 	. 
	inc de			;c384	13 	. 
	rlca			;c385	07 	. 
	rra			;c386	1f 	. 
	cpl			;c387	2f 	/ 
	ld c,01fh		;c388	0e 1f 	. . 
	ccf			;c38a	3f 	? 
	rra			;c38b	1f 	. 
	add hl,de			;c38c	19 	. 
	inc l			;c38d	2c 	, 
	nop			;c38e	00 	. 
	nop			;c38f	00 	. 
	nop			;c390	00 	. 
	nop			;c391	00 	. 
	ret nz			;c392	c0 	. 
	ret po			;c393	e0 	. 
	jr c,$+58		;c394	38 38 	8 8 
	ld a,b			;c396	78 	x 
	ret po			;c397	e0 	. 
	call m,0c47ch		;c398	fc 7c c4 	. | . 
	ret nz			;c39b	c0 	. 
	ret nz			;c39c	c0 	. 
	ret p			;c39d	f0 	. 
	nop			;c39e	00 	. 
	nop			;c39f	00 	. 
	nop			;c3a0	00 	. 
	nop			;c3a1	00 	. 
	rlca			;c3a2	07 	. 
	rrca			;c3a3	0f 	. 
	inc de			;c3a4	13 	. 
	rlca			;c3a5	07 	. 
	rra			;c3a6	1f 	. 
	cpl			;c3a7	2f 	/ 
	rrca			;c3a8	0f 	. 
	rra			;c3a9	1f 	. 
	ld a,01fh		;c3aa	3e 1f 	> . 
	rra			;c3ac	1f 	. 
	cpl			;c3ad	2f 	/ 
	nop			;c3ae	00 	. 
	nop			;c3af	00 	. 
	nop			;c3b0	00 	. 
	nop			;c3b1	00 	. 
	ret nz			;c3b2	c0 	. 
	ret po			;c3b3	e0 	. 
	inc a			;c3b4	3c 	< 
	ld a,h			;c3b5	7c 	| 
	inc a			;c3b6	3c 	< 
	ret po			;c3b7	e0 	. 
	ret nz			;c3b8	c0 	. 
	ret nz			;c3b9	c0 	. 
	call m,0a47ch		;c3ba	fc 7c a4 	. | . 
	ret nz			;c3bd	c0 	. 
	nop			;c3be	00 	. 
	nop			;c3bf	00 	. 
	nop			;c3c0	00 	. 
	nop			;c3c1	00 	. 
	rra			;c3c2	1f 	. 
	ccf			;c3c3	3f 	? 
	ccf			;c3c4	3f 	? 
	ccf			;c3c5	3f 	? 
	ccf			;c3c6	3f 	? 
	ccf			;c3c7	3f 	? 
	rlca			;c3c8	07 	. 
	ld c,03fh		;c3c9	0e 3f 	. ? 
	rra			;c3cb	1f 	. 
	inc c			;c3cc	0c 	. 
	inc c			;c3cd	0c 	. 
	nop			;c3ce	00 	. 
	nop			;c3cf	00 	. 
	nop			;c3d0	00 	. 
	nop			;c3d1	00 	. 
	ret nz			;c3d2	c0 	. 
	ret nz			;c3d3	c0 	. 
	jr c,$+122		;c3d4	38 78 	8 x 
	jr c,$-30		;c3d6	38 e0 	8 . 
	ret m			;c3d8	f8 	. 
	call m,0e060h		;c3d9	fc 60 e0 	. ` . 
	ret nz			;c3dc	c0 	. 
	ret p			;c3dd	f0 	. 
	nop			;c3de	00 	. 
	nop			;c3df	00 	. 
	nop			;c3e0	00 	. 
	nop			;c3e1	00 	. 
	rra			;c3e2	1f 	. 
	ccf			;c3e3	3f 	? 
	ccf			;c3e4	3f 	? 
	ccf			;c3e5	3f 	? 
	ccf			;c3e6	3f 	? 
	rra			;c3e7	1f 	. 
	rlca			;c3e8	07 	. 
	rrca			;c3e9	0f 	. 
	dec e			;c3ea	1d 	. 
	ld a,01fh		;c3eb	3e 1f 	> . 
	inc c			;c3ed	0c 	. 
	nop			;c3ee	00 	. 
	nop			;c3ef	00 	. 
	nop			;c3f0	00 	. 
	nop			;c3f1	00 	. 
	ret nz			;c3f2	c0 	. 
	ret po			;c3f3	e0 	. 
	jr c,$+58		;c3f4	38 38 	8 8 
	ld a,b			;c3f6	78 	x 
	ret po			;c3f7	e0 	. 
	ret nz			;c3f8	c0 	. 
	ret p			;c3f9	f0 	. 
	ret m			;c3fa	f8 	. 
	nop			;c3fb	00 	. 
	and b			;c3fc	a0 	. 
	ret nz			;c3fd	c0 	. 
	nop			;c3fe	00 	. 
	nop			;c3ff	00 	. 
	nop			;c400	00 	. 
	nop			;c401	00 	. 
	nop			;c402	00 	. 
	nop			;c403	00 	. 
	nop			;c404	00 	. 
	ld b,00dh		;c405	06 0d 	. . 
	rra			;c407	1f 	. 
	ccf			;c408	3f 	? 
	ld (hl),03fh		;c409	36 3f 	6 ? 
	ccf			;c40b	3f 	? 
	inc sp			;c40c	33 	3 
	ld hl,00000h		;c40d	21 00 00 	! . . 
	nop			;c410	00 	. 
	nop			;c411	00 	. 
	nop			;c412	00 	. 
	nop			;c413	00 	. 
	nop			;c414	00 	. 
	nop			;c415	00 	. 
	nop			;c416	00 	. 
	ret m			;c417	f8 	. 
	call m,0fccch		;c418	fc cc fc 	. . . 
	call m,084cch		;c41b	fc cc 84 	. . . 
	nop			;c41e	00 	. 
	nop			;c41f	00 	. 
	nop			;c420	00 	. 
	nop			;c421	00 	. 
	ld b,00dh		;c422	06 0d 	. . 
	dec e			;c424	1d 	. 
	ccf			;c425	3f 	? 
	inc a			;c426	3c 	< 
	jr nc,$+50		;c427	30 30 	0 0 
	ld sp,03f3fh		;c429	31 3f 3f 	1 ? ? 
	ld (hl),022h		;c42c	36 22 	6 " 
	nop			;c42e	00 	. 
	nop			;c42f	00 	. 
	nop			;c430	00 	. 
	nop			;c431	00 	. 
	nop			;c432	00 	. 
	nop			;c433	00 	. 
	ret m			;c434	f8 	. 
	call m,000cch		;c435	fc cc 00 	. . . 
	nop			;c438	00 	. 
	sbc a,b			;c439	98 	. 
	call m,06cfch		;c43a	fc fc 6c 	. . l 
	ld b,h			;c43d	44 	D 
	nop			;c43e	00 	. 
	nop			;c43f	00 	. 
	nop			;c440	00 	. 
	nop			;c441	00 	. 
	rrca			;c442	0f 	. 
	rra			;c443	1f 	. 
	jr c,$+61		;c444	38 3b 	8 ; 
	jr c,$+61		;c446	38 3b 	8 ; 
	dec sp			;c448	3b 	; 
	jr c,$+33		;c449	38 1f 	8 . 
	rrca			;c44b	0f 	. 
	ld (bc),a			;c44c	02 	. 
	ld c,000h		;c44d	0e 00 	. . 
	nop			;c44f	00 	. 
	nop			;c450	00 	. 
	nop			;c451	00 	. 
	ret p			;c452	f0 	. 
	ret m			;c453	f8 	. 
	inc a			;c454	3c 	< 
	call m,0fc7ch		;c455	fc 7c fc 	. | . 
	call m,0f83ch		;c458	fc 3c f8 	. < . 
	ret p			;c45b	f0 	. 
	ld (hl),b			;c45c	70 	p 
	nop			;c45d	00 	. 
	nop			;c45e	00 	. 
	nop			;c45f	00 	. 
	nop			;c460	00 	. 
	nop			;c461	00 	. 
	rrca			;c462	0f 	. 
	rra			;c463	1f 	. 
	jr c,$+61		;c464	38 3b 	8 ; 
	jr c,$+61		;c466	38 3b 	8 ; 
	dec sp			;c468	3b 	; 
	jr c,$+33		;c469	38 1f 	8 . 
	rrca			;c46b	0f 	. 
	ld c,000h		;c46c	0e 00 	. . 
	nop			;c46e	00 	. 
	nop			;c46f	00 	. 
	nop			;c470	00 	. 
	nop			;c471	00 	. 
	ret p			;c472	f0 	. 
	ret m			;c473	f8 	. 
	inc a			;c474	3c 	< 
	call m,0fc7ch		;c475	fc 7c fc 	. | . 
	call m,0f83ch		;c478	fc 3c f8 	. < . 
	ret p			;c47b	f0 	. 
	ld b,b			;c47c	40 	@ 
	ld (hl),b			;c47d	70 	p 
	nop			;c47e	00 	. 
	nop			;c47f	00 	. 
	nop			;c480	00 	. 
	nop			;c481	00 	. 
	rrca			;c482	0f 	. 
	rra			;c483	1f 	. 
	dec sp			;c484	3b 	; 
	dec a			;c485	3d 	= 
	ld a,03dh		;c486	3e 3d 	> = 
	dec sp			;c488	3b 	; 
	scf			;c489	37 	7 
	rra			;c48a	1f 	. 
	rrca			;c48b	0f 	. 
	ld c,000h		;c48c	0e 00 	. . 
	nop			;c48e	00 	. 
	nop			;c48f	00 	. 
	nop			;c490	00 	. 
	nop			;c491	00 	. 
	ret p			;c492	f0 	. 
	ret m			;c493	f8 	. 
	cp h			;c494	bc 	. 
	ld a,h			;c495	7c 	| 
	call m,0bc7ch		;c496	fc 7c bc 	. | . 
	call c,0f0f8h		;c499	dc f8 f0 	. . . 
	ld b,b			;c49c	40 	@ 
	ld (hl),b			;c49d	70 	p 
	nop			;c49e	00 	. 
	nop			;c49f	00 	. 
	nop			;c4a0	00 	. 
	nop			;c4a1	00 	. 
	rrca			;c4a2	0f 	. 
	rra			;c4a3	1f 	. 
	dec sp			;c4a4	3b 	; 
	dec a			;c4a5	3d 	= 
	ld a,03dh		;c4a6	3e 3d 	> = 
	dec sp			;c4a8	3b 	; 
	scf			;c4a9	37 	7 
	rra			;c4aa	1f 	. 
	rrca			;c4ab	0f 	. 
	ld (bc),a			;c4ac	02 	. 
	ld c,000h		;c4ad	0e 00 	. . 
	nop			;c4af	00 	. 
	nop			;c4b0	00 	. 
	nop			;c4b1	00 	. 
	ret p			;c4b2	f0 	. 
	ret m			;c4b3	f8 	. 
	cp h			;c4b4	bc 	. 
	ld a,h			;c4b5	7c 	| 
	call m,0bc7ch		;c4b6	fc 7c bc 	. | . 
	call c,0f0f8h		;c4b9	dc f8 f0 	. . . 
	ld (hl),b			;c4bc	70 	p 
	nop			;c4bd	00 	. 
	nop			;c4be	00 	. 
	nop			;c4bf	00 	. 
	nop			;c4c0	00 	. 
	nop			;c4c1	00 	. 
	rrca			;c4c2	0f 	. 
	rra			;c4c3	1f 	. 
	jr c,$+64		;c4c4	38 3e 	8 > 
	ld a,03eh		;c4c6	3e 3e 	> > 
	ld a,03eh		;c4c8	3e 3e 	> > 
	rra			;c4ca	1f 	. 
	rrca			;c4cb	0f 	. 
	ld (bc),a			;c4cc	02 	. 
	ld c,000h		;c4cd	0e 00 	. . 
	nop			;c4cf	00 	. 
	nop			;c4d0	00 	. 
	nop			;c4d1	00 	. 
	ret p			;c4d2	f0 	. 
	ret m			;c4d3	f8 	. 
	inc a			;c4d4	3c 	< 
	call m,0fcfch		;c4d5	fc fc fc 	. . . 
	call m,0f8fch		;c4d8	fc fc f8 	. . . 
	ret p			;c4db	f0 	. 
	ld (hl),b			;c4dc	70 	p 
	nop			;c4dd	00 	. 
	nop			;c4de	00 	. 
	nop			;c4df	00 	. 
	nop			;c4e0	00 	. 
	nop			;c4e1	00 	. 
	rrca			;c4e2	0f 	. 
	rra			;c4e3	1f 	. 
	jr c,$+64		;c4e4	38 3e 	8 > 
	ld a,03eh		;c4e6	3e 3e 	> > 
	ld a,03eh		;c4e8	3e 3e 	> > 
	rra			;c4ea	1f 	. 
	rrca			;c4eb	0f 	. 
	ld c,000h		;c4ec	0e 00 	. . 
	nop			;c4ee	00 	. 
	nop			;c4ef	00 	. 
	nop			;c4f0	00 	. 
	nop			;c4f1	00 	. 
	ret p			;c4f2	f0 	. 
	ret m			;c4f3	f8 	. 
	inc a			;c4f4	3c 	< 
	call m,0fcfch		;c4f5	fc fc fc 	. . . 
	call m,0f8fch		;c4f8	fc fc f8 	. . . 
	ret p			;c4fb	f0 	. 
	ld b,b			;c4fc	40 	@ 
	ld (hl),b			;c4fd	70 	p 
	nop			;c4fe	00 	. 
	nop			;c4ff	00 	. 
	nop			;c500	00 	. 
	nop			;c501	00 	. 
	rrca			;c502	0f 	. 
	rra			;c503	1f 	. 
	jr c,$+61		;c504	38 3b 	8 ; 
	dec sp			;c506	3b 	; 
	jr c,$+60		;c507	38 3a 	8 : 
	dec sp			;c509	3b 	; 
	rra			;c50a	1f 	. 
	rrca			;c50b	0f 	. 
	ld c,000h		;c50c	0e 00 	. . 
	nop			;c50e	00 	. 
	nop			;c50f	00 	. 
	nop			;c510	00 	. 
	nop			;c511	00 	. 
	ret p			;c512	f0 	. 
	ret m			;c513	f8 	. 
	ld a,h			;c514	7c 	| 
	cp h			;c515	bc 	. 
	cp h			;c516	bc 	. 
	ld a,h			;c517	7c 	| 
	call m,0f83ch		;c518	fc 3c f8 	. < . 
	ret p			;c51b	f0 	. 
	ld b,b			;c51c	40 	@ 
	ld (hl),b			;c51d	70 	p 
	nop			;c51e	00 	. 
	nop			;c51f	00 	. 
	nop			;c520	00 	. 
	nop			;c521	00 	. 
	rrca			;c522	0f 	. 
	rra			;c523	1f 	. 
	jr c,$+61		;c524	38 3b 	8 ; 
	dec sp			;c526	3b 	; 
	jr c,$+60		;c527	38 3a 	8 : 
	dec sp			;c529	3b 	; 
	rra			;c52a	1f 	. 
	rrca			;c52b	0f 	. 
	ld (bc),a			;c52c	02 	. 
	ld c,000h		;c52d	0e 00 	. . 
	nop			;c52f	00 	. 
	nop			;c530	00 	. 
	nop			;c531	00 	. 
	ret p			;c532	f0 	. 
	ret m			;c533	f8 	. 
	ld a,h			;c534	7c 	| 
	cp h			;c535	bc 	. 
	cp h			;c536	bc 	. 
	ld a,h			;c537	7c 	| 
	call m,0f83ch		;c538	fc 3c f8 	. < . 
	ret p			;c53b	f0 	. 
	ld (hl),b			;c53c	70 	p 
	nop			;c53d	00 	. 
	nop			;c53e	00 	. 
	nop			;c53f	00 	. 
	nop			;c540	00 	. 
	nop			;c541	00 	. 
	rrca			;c542	0f 	. 
	rra			;c543	1f 	. 
	ld a,03dh		;c544	3e 3d 	> = 
	dec sp			;c546	3b 	; 
	jr c,$+61		;c547	38 3b 	8 ; 
	dec sp			;c549	3b 	; 
	rra			;c54a	1f 	. 
	rrca			;c54b	0f 	. 
	ld (bc),a			;c54c	02 	. 
	ld c,000h		;c54d	0e 00 	. . 
	nop			;c54f	00 	. 
	nop			;c550	00 	. 
	nop			;c551	00 	. 
	ret p			;c552	f0 	. 
	ret m			;c553	f8 	. 
	ld a,h			;c554	7c 	| 
	cp h			;c555	bc 	. 
	call c,0dc1ch		;c556	dc 1c dc 	. . . 
	call c,0f0f8h		;c559	dc f8 f0 	. . . 
	ld (hl),b			;c55c	70 	p 
	nop			;c55d	00 	. 
	nop			;c55e	00 	. 
	nop			;c55f	00 	. 
	nop			;c560	00 	. 
	nop			;c561	00 	. 
	rrca			;c562	0f 	. 
	rra			;c563	1f 	. 
	ld a,03dh		;c564	3e 3d 	> = 
	dec sp			;c566	3b 	; 
	jr c,$+61		;c567	38 3b 	8 ; 
	dec sp			;c569	3b 	; 
	rra			;c56a	1f 	. 
	rrca			;c56b	0f 	. 
	ld c,000h		;c56c	0e 00 	. . 
	nop			;c56e	00 	. 
	nop			;c56f	00 	. 
	nop			;c570	00 	. 
	nop			;c571	00 	. 
	ret p			;c572	f0 	. 
	ret m			;c573	f8 	. 
	ld a,h			;c574	7c 	| 
	cp h			;c575	bc 	. 
	call c,0dc1ch		;c576	dc 1c dc 	. . . 
	call c,0f0f8h		;c579	dc f8 f0 	. . . 
	ld b,b			;c57c	40 	@ 
	ld (hl),b			;c57d	70 	p 
	nop			;c57e	00 	. 
	nop			;c57f	00 	. 
	nop			;c580	00 	. 
	nop			;c581	00 	. 
	nop			;c582	00 	. 
	ld bc,01f0eh		;c583	01 0e 1f 	. . . 
	ccf			;c586	3f 	? 
	ccf			;c587	3f 	? 
	ccf			;c588	3f 	? 
	ccf			;c589	3f 	? 
	rra			;c58a	1f 	. 
	rra			;c58b	1f 	. 
	rrca			;c58c	0f 	. 
	inc bc			;c58d	03 	. 
	nop			;c58e	00 	. 
	nop			;c58f	00 	. 
	nop			;c590	00 	. 
	nop			;c591	00 	. 
	nop			;c592	00 	. 
	ret nz			;c593	c0 	. 
	ld (hl),b			;c594	70 	p 
	ret pe			;c595	e8 	. 
	ld e,h			;c596	5c 	\ 
	cp h			;c597	bc 	. 
	call m,0b8dch		;c598	fc dc b8 	. . . 
	cp b			;c59b	b8 	. 
	ld (hl),b			;c59c	70 	p 
	ret nz			;c59d	c0 	. 
	nop			;c59e	00 	. 
	nop			;c59f	00 	. 
	nop			;c5a0	00 	. 
	nop			;c5a1	00 	. 
	nop			;c5a2	00 	. 
	ld (bc),a			;c5a3	02 	. 
	ld c,01eh		;c5a4	0e 1e 	. . 
	ld a,03eh		;c5a6	3e 3e 	> > 
	ld a,03eh		;c5a8	3e 3e 	> > 
	ld e,01eh		;c5aa	1e 1e 	. . 
	ld c,006h		;c5ac	0e 06 	. . 
	nop			;c5ae	00 	. 
	nop			;c5af	00 	. 
	nop			;c5b0	00 	. 
	nop			;c5b1	00 	. 
	nop			;c5b2	00 	. 
	ld b,b			;c5b3	40 	@ 
	ld (hl),b			;c5b4	70 	p 
	ld a,b			;c5b5	78 	x 
	ld a,h			;c5b6	7c 	| 
	ld a,h			;c5b7	7c 	| 
	ld a,h			;c5b8	7c 	| 
	ld a,h			;c5b9	7c 	| 
	ld a,b			;c5ba	78 	x 
	ld a,b			;c5bb	78 	x 
	ld (hl),b			;c5bc	70 	p 
	ld h,b			;c5bd	60 	` 
	nop			;c5be	00 	. 
	nop			;c5bf	00 	. 
	nop			;c5c0	00 	. 
	nop			;c5c1	00 	. 
	nop			;c5c2	00 	. 
	nop			;c5c3	00 	. 
	nop			;c5c4	00 	. 
	nop			;c5c5	00 	. 
	nop			;c5c6	00 	. 
	nop			;c5c7	00 	. 
	nop			;c5c8	00 	. 
	rst 38h			;c5c9	ff 	. 
	rst 38h			;c5ca	ff 	. 
	cp 07eh		;c5cb	fe 7e 	. ~ 
	inc a			;c5cd	3c 	< 
	nop			;c5ce	00 	. 
	nop			;c5cf	00 	. 
	nop			;c5d0	00 	. 
	nop			;c5d1	00 	. 
	nop			;c5d2	00 	. 
	nop			;c5d3	00 	. 
	nop			;c5d4	00 	. 
	nop			;c5d5	00 	. 
	nop			;c5d6	00 	. 
	nop			;c5d7	00 	. 
	nop			;c5d8	00 	. 
	rst 38h			;c5d9	ff 	. 
	rst 38h			;c5da	ff 	. 
	ld a,a			;c5db	7f 	 
	ld a,(hl)			;c5dc	7e 	~ 
	inc a			;c5dd	3c 	< 
	nop			;c5de	00 	. 
	nop			;c5df	00 	. 
	nop			;c5e0	00 	. 
	nop			;c5e1	00 	. 
	nop			;c5e2	00 	. 
	nop			;c5e3	00 	. 
	nop			;c5e4	00 	. 
	nop			;c5e5	00 	. 
	nop			;c5e6	00 	. 
	nop			;c5e7	00 	. 
	nop			;c5e8	00 	. 
	nop			;c5e9	00 	. 
	rra			;c5ea	1f 	. 
	ccf			;c5eb	3f 	? 
	rra			;c5ec	1f 	. 
	ccf			;c5ed	3f 	? 
	nop			;c5ee	00 	. 
	nop			;c5ef	00 	. 
	nop			;c5f0	00 	. 
	nop			;c5f1	00 	. 
	nop			;c5f2	00 	. 
	nop			;c5f3	00 	. 
	nop			;c5f4	00 	. 
	nop			;c5f5	00 	. 
	nop			;c5f6	00 	. 
	nop			;c5f7	00 	. 
	nop			;c5f8	00 	. 
	nop			;c5f9	00 	. 
	ret m			;c5fa	f8 	. 
	call m,0fcf8h		;c5fb	fc f8 fc 	. . . 
	nop			;c5fe	00 	. 
	nop			;c5ff	00 	. 
	nop			;c600	00 	. 
	nop			;c601	00 	. 
	rlca			;c602	07 	. 
	add hl,bc			;c603	09 	. 
	ld (de),a			;c604	12 	. 
	inc h			;c605	24 	$ 
	jr c,$+41		;c606	38 27 	8 ' 
	inc d			;c608	14 	. 
	ld (de),a			;c609	12 	. 
	add hl,bc			;c60a	09 	. 
	inc b			;c60b	04 	. 
	ld (bc),a			;c60c	02 	. 
	ld bc,00000h		;c60d	01 00 00 	. . . 
	nop			;c610	00 	. 
	nop			;c611	00 	. 
	ret po			;c612	e0 	. 
	sub b			;c613	90 	. 
	ld c,b			;c614	48 	H 
	inc h			;c615	24 	$ 
	inc e			;c616	1c 	. 
	call po,04828h		;c617	e4 28 48 	. ( H 
	sub b			;c61a	90 	. 
	jr nz,$+66		;c61b	20 40 	  @ 
	add a,b			;c61d	80 	. 
	nop			;c61e	00 	. 
	nop			;c61f	00 	. 
	nop			;c620	00 	. 
	nop			;c621	00 	. 
	nop			;c622	00 	. 
	nop			;c623	00 	. 
	nop			;c624	00 	. 
	nop			;c625	00 	. 
	nop			;c626	00 	. 
	ld bc,00001h		;c627	01 01 00 	. . . 
	nop			;c62a	00 	. 
	nop			;c62b	00 	. 
	nop			;c62c	00 	. 
	nop			;c62d	00 	. 
	nop			;c62e	00 	. 
	nop			;c62f	00 	. 
	nop			;c630	00 	. 
	nop			;c631	00 	. 
	nop			;c632	00 	. 
	nop			;c633	00 	. 
	nop			;c634	00 	. 
	nop			;c635	00 	. 
	nop			;c636	00 	. 
	add a,b			;c637	80 	. 
	add a,b			;c638	80 	. 
	nop			;c639	00 	. 
	nop			;c63a	00 	. 
	nop			;c63b	00 	. 
	nop			;c63c	00 	. 
	nop			;c63d	00 	. 
	nop			;c63e	00 	. 
	nop			;c63f	00 	. 
	nop			;c640	00 	. 
	nop			;c641	00 	. 
	nop			;c642	00 	. 
	nop			;c643	00 	. 
	nop			;c644	00 	. 
	nop			;c645	00 	. 
	ld bc,00102h		;c646	01 02 01 	. . . 
	nop			;c649	00 	. 
	nop			;c64a	00 	. 
	nop			;c64b	00 	. 
	nop			;c64c	00 	. 
	nop			;c64d	00 	. 
	nop			;c64e	00 	. 
	nop			;c64f	00 	. 
	nop			;c650	00 	. 
	nop			;c651	00 	. 
	nop			;c652	00 	. 
	nop			;c653	00 	. 
	nop			;c654	00 	. 
	nop			;c655	00 	. 
	nop			;c656	00 	. 
	add a,b			;c657	80 	. 
	nop			;c658	00 	. 
	nop			;c659	00 	. 
	nop			;c65a	00 	. 
	nop			;c65b	00 	. 
	nop			;c65c	00 	. 
	nop			;c65d	00 	. 
	nop			;c65e	00 	. 
	nop			;c65f	00 	. 
	nop			;c660	00 	. 
	nop			;c661	00 	. 
	nop			;c662	00 	. 
	nop			;c663	00 	. 
	nop			;c664	00 	. 
	ld bc,00402h		;c665	01 02 04 	. . . 
	ld (bc),a			;c668	02 	. 
	ld bc,00000h		;c669	01 00 00 	. . . 
	nop			;c66c	00 	. 
	nop			;c66d	00 	. 
	nop			;c66e	00 	. 
	nop			;c66f	00 	. 
	nop			;c670	00 	. 
	nop			;c671	00 	. 
	nop			;c672	00 	. 
	nop			;c673	00 	. 
	nop			;c674	00 	. 
	nop			;c675	00 	. 
	add a,b			;c676	80 	. 
	ld b,b			;c677	40 	@ 
	add a,b			;c678	80 	. 
	nop			;c679	00 	. 
	nop			;c67a	00 	. 
	nop			;c67b	00 	. 
	nop			;c67c	00 	. 
	nop			;c67d	00 	. 
	nop			;c67e	00 	. 
	nop			;c67f	00 	. 
	nop			;c680	00 	. 
	nop			;c681	00 	. 
	nop			;c682	00 	. 
	nop			;c683	00 	. 
	ld bc,00004h		;c684	01 04 00 	. . . 
	ex af,af'			;c687	08 	. 
	nop			;c688	00 	. 
	inc b			;c689	04 	. 
	ld bc,00000h		;c68a	01 00 00 	. . . 
	nop			;c68d	00 	. 
	nop			;c68e	00 	. 
	nop			;c68f	00 	. 
	nop			;c690	00 	. 
	nop			;c691	00 	. 
	nop			;c692	00 	. 
	nop			;c693	00 	. 
	nop			;c694	00 	. 
	ld b,b			;c695	40 	@ 
	nop			;c696	00 	. 
	jr nz,$+2		;c697	20 00 	  . 
	ld b,b			;c699	40 	@ 
	nop			;c69a	00 	. 
	nop			;c69b	00 	. 
	nop			;c69c	00 	. 
	nop			;c69d	00 	. 
	nop			;c69e	00 	. 
	nop			;c69f	00 	. 
	nop			;c6a0	00 	. 
	nop			;c6a1	00 	. 
	nop			;c6a2	00 	. 
	ld bc,00008h		;c6a3	01 08 00 	. . . 
	nop			;c6a6	00 	. 
	djnz $+2		;c6a7	10 00 	. . 
	nop			;c6a9	00 	. 
	add a,b			;c6aa	80 	. 
	ld bc,00000h		;c6ab	01 00 00 	. . . 
	nop			;c6ae	00 	. 
	nop			;c6af	00 	. 
	nop			;c6b0	00 	. 
	nop			;c6b1	00 	. 
	nop			;c6b2	00 	. 
	nop			;c6b3	00 	. 
	jr nz,$+2		;c6b4	20 00 	  . 
	nop			;c6b6	00 	. 
	djnz $+2		;c6b7	10 00 	. . 
	nop			;c6b9	00 	. 
	jr nz,$+2		;c6ba	20 00 	  . 
	nop			;c6bc	00 	. 
	nop			;c6bd	00 	. 
	nop			;c6be	00 	. 
	nop			;c6bf	00 	. 
	nop			;c6c0	00 	. 
	nop			;c6c1	00 	. 
	ld bc,00010h		;c6c2	01 10 00 	. . . 
	nop			;c6c5	00 	. 
	nop			;c6c6	00 	. 
	jr nz,$+2		;c6c7	20 00 	  . 
	nop			;c6c9	00 	. 
	nop			;c6ca	00 	. 
	djnz $+3		;c6cb	10 01 	. . 
	nop			;c6cd	00 	. 
	nop			;c6ce	00 	. 
	nop			;c6cf	00 	. 
	nop			;c6d0	00 	. 
	nop			;c6d1	00 	. 
	nop			;c6d2	00 	. 
	djnz $+2		;c6d3	10 00 	. . 
	nop			;c6d5	00 	. 
	nop			;c6d6	00 	. 
	ex af,af'			;c6d7	08 	. 
	nop			;c6d8	00 	. 
	nop			;c6d9	00 	. 
	nop			;c6da	00 	. 
	djnz $+2		;c6db	10 00 	. . 
	nop			;c6dd	00 	. 
	nop			;c6de	00 	. 
	nop			;c6df	00 	. 
	nop			;c6e0	00 	. 
	ld bc,00020h		;c6e1	01 20 00 	.   . 
	nop			;c6e4	00 	. 
	nop			;c6e5	00 	. 
	nop			;c6e6	00 	. 
	ld b,b			;c6e7	40 	@ 
	nop			;c6e8	00 	. 
	nop			;c6e9	00 	. 
	nop			;c6ea	00 	. 
	nop			;c6eb	00 	. 
	jr nz,$+2		;c6ec	20 00 	  . 
	ld bc,00000h		;c6ee	01 00 00 	. . . 
	nop			;c6f1	00 	. 
	ex af,af'			;c6f2	08 	. 
	nop			;c6f3	00 	. 
	nop			;c6f4	00 	. 
	nop			;c6f5	00 	. 
	nop			;c6f6	00 	. 
	nop			;c6f7	00 	. 
	nop			;c6f8	00 	. 
	nop			;c6f9	00 	. 
	nop			;c6fa	00 	. 
	nop			;c6fb	00 	. 
	ex af,af'			;c6fc	08 	. 
	nop			;c6fd	00 	. 
	nop			;c6fe	00 	. 
	nop			;c6ff	00 	. 
	ld bc,03100h		;c700	01 00 31 	. . 1 
	rst 0			;c703	c7 	. 
	ld (bc),a			;c704	02 	. 
	ex af,af'			;c705	08 	. 
	add hl,sp			;c706	39 	9 
	rst 0			;c707	c7 	. 
	ld (bc),a			;c708	02 	. 
	djnz $+75		;c709	10 49 	. I 
	rst 0			;c70b	c7 	. 
	inc b			;c70c	04 	. 
	jr $+91		;c70d	18 59 	. Y 
	rst 0			;c70f	c7 	. 
	ld b,020h		;c710	06 20 	.   
	ld a,c			;c712	79 	y 
	rst 0			;c713	c7 	. 
	rrca			;c714	0f 	. 
	jr z,$-53		;c715	28 c9 	( . 
	rst 0			;c717	c7 	. 
	djnz $+58		;c718	10 38 	. 8 
	ld b,c			;c71a	41 	A 
	ret z			;c71b	c8 	. 
	dec b			;c71c	05 	. 
	ld c,b			;c71d	48 	H 
	pop bc			;c71e	c1 	. 
	ret z			;c71f	c8 	. 
	dec b			;c720	05 	. 
	ld d,b			;c721	50 	P 
	jp (hl)			;c722	e9 	. 
	ret z			;c723	c8 	. 
	ex af,af'			;c724	08 	. 
	ld e,b			;c725	58 	X 
	ld de,004c9h		;c726	11 c9 04 	. . . 
	ld (hl),b			;c729	70 	p 
	xor c			;c72a	a9 	. 
	rst 0			;c72b	c7 	. 
	ld (bc),a			;c72c	02 	. 
	ld a,b			;c72d	78 	x 
	ret			;c72e	c9 	. 
	rst 0			;c72f	c7 	. 
	nop			;c730	00 	. 
	nop			;c731	00 	. 
	nop			;c732	00 	. 
	nop			;c733	00 	. 
	nop			;c734	00 	. 
	nop			;c735	00 	. 
	nop			;c736	00 	. 
	nop			;c737	00 	. 
	nop			;c738	00 	. 
	nop			;c739	00 	. 
	nop			;c73a	00 	. 
	nop			;c73b	00 	. 
	nop			;c73c	00 	. 
	nop			;c73d	00 	. 
	nop			;c73e	00 	. 
	ld bc,00002h		;c73f	01 02 00 	. . . 
	nop			;c742	00 	. 
	nop			;c743	00 	. 
	jr nc,$+74		;c744	30 48 	0 H 
	adc a,b			;c746	88 	. 
	ex af,af'			;c747	08 	. 
	ex af,af'			;c748	08 	. 
	inc b			;c749	04 	. 
	ld c,01bh		;c74a	0e 1b 	. . 
	dec e			;c74c	1d 	. 
	rra			;c74d	1f 	. 
	ld c,000h		;c74e	0e 00 	. . 
	nop			;c750	00 	. 
	djnz $+58		;c751	10 38 	. 8 
	ld l,h			;c753	6c 	l 
	ld (hl),h			;c754	74 	t 
	ld a,h			;c755	7c 	| 
	jr c,$+2		;c756	38 00 	8 . 
	nop			;c758	00 	. 
	nop			;c759	00 	. 
	nop			;c75a	00 	. 
	ld bc,00703h		;c75b	01 03 07 	. . . 
	ld c,01ch		;c75e	0e 1c 	. . 
	dec e			;c760	1d 	. 
	nop			;c761	00 	. 
	nop			;c762	00 	. 
	add a,b			;c763	80 	. 
	ret nz			;c764	c0 	. 
	ret po			;c765	e0 	. 
	ret p			;c766	f0 	. 
	ret m			;c767	f8 	. 
	ret m			;c768	f8 	. 
	add hl,sp			;c769	39 	9 
	dec sp			;c76a	3b 	; 
	rra			;c76b	1f 	. 
	rrca			;c76c	0f 	. 
	inc bc			;c76d	03 	. 
	nop			;c76e	00 	. 
	nop			;c76f	00 	. 
	nop			;c770	00 	. 
	call m,0f8fch		;c771	fc fc f8 	. . . 
	ret p			;c774	f0 	. 
	ret nz			;c775	c0 	. 
	nop			;c776	00 	. 
	nop			;c777	00 	. 
	nop			;c778	00 	. 
	nop			;c779	00 	. 
	nop			;c77a	00 	. 
	ld hl,(0163fh)		;c77b	2a 3f 16 	* ? . 
	ccf			;c77e	3f 	? 
	rla			;c77f	17 	. 
	ccf			;c780	3f 	? 
	nop			;c781	00 	. 
	nop			;c782	00 	. 
	ret nz			;c783	c0 	. 
	add a,b			;c784	80 	. 
	ret nz			;c785	c0 	. 
	add a,b			;c786	80 	. 
	ld l,h			;c787	6c 	l 
	ret m			;c788	f8 	. 
	rra			;c789	1f 	. 
	dec (hl)			;c78a	35 	5 
	inc bc			;c78b	03 	. 
	ld bc,00303h		;c78c	01 03 03 	. . . 
	nop			;c78f	00 	. 
	nop			;c790	00 	. 
	ld l,h			;c791	6c 	l 
	ret m			;c792	f8 	. 
	call m,0fc68h		;c793	fc 68 fc 	. h . 
	ld d,h			;c796	54 	T 
	nop			;c797	00 	. 
	nop			;c798	00 	. 
	ccf			;c799	3f 	? 
	ld a,031h		;c79a	3e 31 	> 1 
	rrca			;c79c	0f 	. 
	ccf			;c79d	3f 	? 
	jr c,$+2		;c79e	38 00 	8 . 
	nop			;c7a0	00 	. 
	ret p			;c7a1	f0 	. 
	ex af,af'			;c7a2	08 	. 
	ret m			;c7a3	f8 	. 
	ret m			;c7a4	f8 	. 
	nop			;c7a5	00 	. 
	nop			;c7a6	00 	. 
	nop			;c7a7	00 	. 
	nop			;c7a8	00 	. 
	nop			;c7a9	00 	. 
	nop			;c7aa	00 	. 
	rra			;c7ab	1f 	. 
	jr nz,$+34		;c7ac	20 20 	    
	jr nz,$+34		;c7ae	20 20 	    
	jr $+6		;c7b0	18 04 	. . 
	ex af,af'			;c7b2	08 	. 
	ex af,af'			;c7b3	08 	. 
	djnz $+10		;c7b4	10 08 	. . 
	rrca			;c7b6	0f 	. 
	nop			;c7b7	00 	. 
	nop			;c7b8	00 	. 
	nop			;c7b9	00 	. 
	nop			;c7ba	00 	. 
	ret nz			;c7bb	c0 	. 
	jr nz,$+26		;c7bc	20 18 	  . 
	ld c,b			;c7be	48 	H 
	ex af,af'			;c7bf	08 	. 
	djnz $+34		;c7c0	10 20 	.   
	jr c,$+14		;c7c2	38 0c 	8 . 
	djnz $+34		;c7c4	10 20 	.   
	ret p			;c7c6	f0 	. 
	nop			;c7c7	00 	. 
	nop			;c7c8	00 	. 
	nop			;c7c9	00 	. 
	nop			;c7ca	00 	. 
	jr c,$+122		;c7cb	38 78 	8 x 
	ld a,h			;c7cd	7c 	| 
	halt			;c7ce	76 	v 
	ld d,(hl)			;c7cf	56 	V 
	ld e,h			;c7d0	5c 	\ 
	jr $+58		;c7d1	18 38 	. 8 
	ld a,h			;c7d3	7c 	| 
	ld a,h			;c7d4	7c 	| 
	jr z,$+64		;c7d5	28 3e 	( > 
	nop			;c7d7	00 	. 
	nop			;c7d8	00 	. 
	nop			;c7d9	00 	. 
	nop			;c7da	00 	. 
	nop			;c7db	00 	. 
	nop			;c7dc	00 	. 
	ld bc,00d03h		;c7dd	01 03 0d 	. . . 
	ld e,000h		;c7e0	1e 00 	. . 
	nop			;c7e2	00 	. 
	nop			;c7e3	00 	. 
	nop			;c7e4	00 	. 
	add a,b			;c7e5	80 	. 
	ret nz			;c7e6	c0 	. 
	or b			;c7e7	b0 	. 
	ld a,b			;c7e8	78 	x 
	nop			;c7e9	00 	. 
	nop			;c7ea	00 	. 
	nop			;c7eb	00 	. 
	inc bc			;c7ec	03 	. 
	rlca			;c7ed	07 	. 
	rrca			;c7ee	0f 	. 
	rra			;c7ef	1f 	. 
	ccf			;c7f0	3f 	? 
	nop			;c7f1	00 	. 
	nop			;c7f2	00 	. 
	nop			;c7f3	00 	. 
	ret nz			;c7f4	c0 	. 
	ret m			;c7f5	f8 	. 
	ret m			;c7f6	f8 	. 
	ret m			;c7f7	f8 	. 
	ret pe			;c7f8	e8 	. 
	nop			;c7f9	00 	. 
	nop			;c7fa	00 	. 
	rlca			;c7fb	07 	. 
	add hl,bc			;c7fc	09 	. 
	ld (de),a			;c7fd	12 	. 
	inc h			;c7fe	24 	$ 
	jr c,$+41		;c7ff	38 27 	8 ' 
	nop			;c801	00 	. 
	nop			;c802	00 	. 
	ret po			;c803	e0 	. 
	sub b			;c804	90 	. 
	ld c,b			;c805	48 	H 
	inc h			;c806	24 	$ 
	inc e			;c807	1c 	. 
	call po,01214h		;c808	e4 14 12 	. . . 
	add hl,bc			;c80b	09 	. 
	inc b			;c80c	04 	. 
	ld (bc),a			;c80d	02 	. 
	ld bc,00000h		;c80e	01 00 00 	. . . 
	jr z,$+74		;c811	28 48 	( H 
	sub b			;c813	90 	. 
	jr nz,$+66		;c814	20 40 	  @ 
	add a,b			;c816	80 	. 
	nop			;c817	00 	. 
	nop			;c818	00 	. 
	cp 0feh		;c819	fe fe 	. . 
	ret nz			;c81b	c0 	. 
	ret m			;c81c	f8 	. 
	ret m			;c81d	f8 	. 
	ret nz			;c81e	c0 	. 
	cp 0feh		;c81f	fe fe 	. . 
	add a,d			;c821	82 	. 
	add a,06ch		;c822	c6 6c 	. l 
	jr c,$+58		;c824	38 38 	8 8 
	ld l,h			;c826	6c 	l 
	add a,082h		;c827	c6 82 	. . 
	call m,030fch		;c829	fc fc 30 	. . 0 
	jr nc,$+50		;c82c	30 30 	0 0 
	jr nc,$+50		;c82e	30 30 	0 0 
	jr nc,$-6		;c830	30 f8 	0 . 
	call m,0c6c6h		;c832	fc c6 c6 	. . . 
	cp 0f0h		;c835	fe f0 	. . 
	ret z			;c837	c8 	. 
	call z,07c78h		;c838	cc 78 7c 	. x | 
	call z,0fefch		;c83b	cc fc fe 	. . . 
	add a,0c6h		;c83e	c6 c6 	. . 
	add a,03fh		;c840	c6 3f 	. ? 
	dec hl			;c842	2b 	+ 
	ld a,(bc)			;c843	0a 	. 
	ld bc,00301h		;c844	01 01 03 	. . . 
	nop			;c847	00 	. 
	nop			;c848	00 	. 
	call m,060b4h		;c849	fc b4 60 	. . ` 
	add a,b			;c84c	80 	. 
	add a,b			;c84d	80 	. 
	ret nz			;c84e	c0 	. 
	nop			;c84f	00 	. 
	nop			;c850	00 	. 
	rst 38h			;c851	ff 	. 
	rst 38h			;c852	ff 	. 
	ret nz			;c853	c0 	. 
	ret nz			;c854	c0 	. 
	ret nz			;c855	c0 	. 
	ret nz			;c856	c0 	. 
	ret nz			;c857	c0 	. 
	ret nz			;c858	c0 	. 
	ret nz			;c859	c0 	. 
	ret nz			;c85a	c0 	. 
	ret nz			;c85b	c0 	. 
	ret nz			;c85c	c0 	. 
	ret nz			;c85d	c0 	. 
	ret nz			;c85e	c0 	. 
	ret nz			;c85f	c0 	. 
	ret nz			;c860	c0 	. 
	ret nz			;c861	c0 	. 
	ret nz			;c862	c0 	. 
	ret nz			;c863	c0 	. 
	ret nz			;c864	c0 	. 
	ret nz			;c865	c0 	. 
	ret nz			;c866	c0 	. 
	rst 38h			;c867	ff 	. 
	rst 38h			;c868	ff 	. 
	rst 38h			;c869	ff 	. 
	rst 38h			;c86a	ff 	. 
	nop			;c86b	00 	. 
	nop			;c86c	00 	. 
	nop			;c86d	00 	. 
	nop			;c86e	00 	. 
	nop			;c86f	00 	. 
	nop			;c870	00 	. 
	nop			;c871	00 	. 
	nop			;c872	00 	. 
	nop			;c873	00 	. 
	nop			;c874	00 	. 
	nop			;c875	00 	. 
	nop			;c876	00 	. 
	rst 38h			;c877	ff 	. 
	rst 38h			;c878	ff 	. 
	rst 38h			;c879	ff 	. 
	rst 38h			;c87a	ff 	. 
	inc bc			;c87b	03 	. 
	inc bc			;c87c	03 	. 
	inc bc			;c87d	03 	. 
	inc bc			;c87e	03 	. 
	inc bc			;c87f	03 	. 
	inc bc			;c880	03 	. 
	inc bc			;c881	03 	. 
	inc bc			;c882	03 	. 
	inc bc			;c883	03 	. 
	inc bc			;c884	03 	. 
	inc bc			;c885	03 	. 
	inc bc			;c886	03 	. 
	inc bc			;c887	03 	. 
	inc bc			;c888	03 	. 
	inc bc			;c889	03 	. 
	inc bc			;c88a	03 	. 
	inc bc			;c88b	03 	. 
	inc bc			;c88c	03 	. 
	inc bc			;c88d	03 	. 
	inc bc			;c88e	03 	. 
	rst 38h			;c88f	ff 	. 
	rst 38h			;c890	ff 	. 
	ld hl,02262h		;c891	21 62 22 	! b " 
	ld hl,02220h		;c894	21 20 22 	!   " 
	ld (hl),c			;c897	71 	q 
	nop			;c898	00 	. 
	rst 8			;c899	cf 	. 
	ld (0c202h),hl		;c89a	22 02 c2 	" . . 
	ld (0c222h),hl		;c89d	22 22 c2 	" " . 
	nop			;c8a0	00 	. 
	add a,b			;c8a1	80 	. 
	nop			;c8a2	00 	. 
	nop			;c8a3	00 	. 
	nop			;c8a4	00 	. 
	nop			;c8a5	00 	. 
	nop			;c8a6	00 	. 
	nop			;c8a7	00 	. 
	nop			;c8a8	00 	. 
	ld (hl),d			;c8a9	72 	r 
	adc a,d			;c8aa	8a 	. 
	dec bc			;c8ab	0b 	. 
	ld (08242h),a		;c8ac	32 42 82 	2 B . 
	jp m,02f00h		;c8af	fa 00 2f 	. . / 
	jr z,$+42		;c8b2	28 28 	( ( 
	xor b			;c8b4	a8 	. 
	ld l,b			;c8b5	68 	h 
	jr z,$+49		;c8b6	28 2f 	( / 
	nop			;c8b8	00 	. 
	nop			;c8b9	00 	. 
	add a,b			;c8ba	80 	. 
	add a,b			;c8bb	80 	. 
	add a,b			;c8bc	80 	. 
	add a,b			;c8bd	80 	. 
	add a,b			;c8be	80 	. 
	nop			;c8bf	00 	. 
	nop			;c8c0	00 	. 
	cp 0feh		;c8c1	fe fe 	. . 
	ret nz			;c8c3	c0 	. 
	ret m			;c8c4	f8 	. 
	ret m			;c8c5	f8 	. 
	ret nz			;c8c6	c0 	. 
	cp 0feh		;c8c7	fe fe 	. . 
	add a,d			;c8c9	82 	. 
	add a,06ch		;c8ca	c6 6c 	. l 
	jr c,$+58		;c8cc	38 38 	8 8 
	ld l,h			;c8ce	6c 	l 
	add a,082h		;c8cf	c6 82 	. . 
	call m,030fch		;c8d1	fc fc 30 	. . 0 
	jr nc,$+50		;c8d4	30 30 	0 0 
	jr nc,$+50		;c8d6	30 30 	0 0 
	jr nc,$-6		;c8d8	30 f8 	0 . 
	call m,0c6c6h		;c8da	fc c6 c6 	. . . 
	cp 0f0h		;c8dd	fe f0 	. . 
	ret z			;c8df	c8 	. 
	call z,07c78h		;c8e0	cc 78 7c 	. x | 
	call z,0fefch		;c8e3	cc fc fe 	. . . 
	add a,0c6h		;c8e6	c6 c6 	. . 
	add a,01eh		;c8e8	c6 1e 	. . 
	ld e,0ffh		;c8ea	1e ff 	. . 
	rst 38h			;c8ec	ff 	. 
	pop hl			;c8ed	e1 	. 
	pop hl			;c8ee	e1 	. 
	rst 38h			;c8ef	ff 	. 
	rst 38h			;c8f0	ff 	. 
	pop af			;c8f1	f1 	. 
	ex (sp),hl			;c8f2	e3 	. 
	rst 0			;c8f3	c7 	. 
	adc a,a			;c8f4	8f 	. 
	rra			;c8f5	1f 	. 
	ld a,07ch		;c8f6	3e 7c 	> | 
	ret m			;c8f8	f8 	. 
	add a,c			;c8f9	81 	. 
	ld b,d			;c8fa	42 	B 
	inc h			;c8fb	24 	$ 
	jr $+26		;c8fc	18 18 	. . 
	inc h			;c8fe	24 	$ 
	ld b,d			;c8ff	42 	B 
	add a,c			;c900	81 	. 
	inc sp			;c901	33 	3 
	ld h,(hl)			;c902	66 	f 
	call z,0cc88h		;c903	cc 88 cc 	. . . 
	ld h,(hl)			;c906	66 	f 
	inc sp			;c907	33 	3 
	ld de,066c3h		;c908	11 c3 66 	. . f 
	inc a			;c90b	3c 	< 
	nop			;c90c	00 	. 
	jp 03c66h		;c90d	c3 66 3c 	. f < 
	nop			;c910	00 	. 
	ret nz			;c911	c0 	. 
	ret nz			;c912	c0 	. 
	add a,b			;c913	80 	. 
	add a,b			;c914	80 	. 
	ret nz			;c915	c0 	. 
	ret nz			;c916	c0 	. 
	add a,b			;c917	80 	. 
	add a,b			;c918	80 	. 
	ld bc,00301h		;c919	01 01 03 	. . . 
	inc bc			;c91c	03 	. 
	ld bc,00301h		;c91d	01 01 03 	. . . 
	inc bc			;c920	03 	. 
	rst 38h			;c921	ff 	. 
	call z,00000h		;c922	cc 00 00 	. . . 
	nop			;c925	00 	. 
	nop			;c926	00 	. 
	nop			;c927	00 	. 
	nop			;c928	00 	. 
	nop			;c929	00 	. 
	nop			;c92a	00 	. 
	nop			;c92b	00 	. 
	nop			;c92c	00 	. 
	nop			;c92d	00 	. 
	nop			;c92e	00 	. 
	inc sp			;c92f	33 	3 
	rst 38h			;c930	ff 	. 
	rst 38h			;c931	ff 	. 
	call z,08080h		;c932	cc 80 80 	. . . 
	ret nz			;c935	c0 	. 
	ret nz			;c936	c0 	. 
	add a,b			;c937	80 	. 
	add a,b			;c938	80 	. 
	rst 38h			;c939	ff 	. 
	call 00303h		;c93a	cd 03 03 	. . . 
	ld bc,00301h		;c93d	01 01 03 	. . . 
	inc bc			;c940	03 	. 
	ret nz			;c941	c0 	. 
	ret nz			;c942	c0 	. 
	add a,b			;c943	80 	. 
	add a,b			;c944	80 	. 
	ret nz			;c945	c0 	. 
	ret nz			;c946	c0 	. 
	or e			;c947	b3 	. 
	rst 38h			;c948	ff 	. 
	ld bc,00301h		;c949	01 01 03 	. . . 
	inc bc			;c94c	03 	. 
	ld bc,03301h		;c94d	01 01 33 	. . 3 
	rst 38h			;c950	ff 	. 
	nop			;c951	00 	. 
	call 01f61h		;c952	cd 61 1f 	. a . 
	jp 01ff4h		;c955	c3 f4 1f 	. . . 
	ld hl,0ca40h		;c958	21 40 ca 	! @ . 
	ld b,009h		;c95b	06 09 	. . 
	jp 01feeh		;c95d	c3 ee 1f 	. . . 
	ld b,001h		;c960	06 01 	. . 
	call 01ff1h		;c962	cd f1 1f 	. . . 
	ld b,003h		;c965	06 03 	. . 
	call 01ff1h		;c967	cd f1 1f 	. . . 
	ld a,(0702bh)		;c96a	3a 2b 70 	: + p 
	and 0c0h		;c96d	e6 c0 	. . 
	or 002h		;c96f	f6 02 	. . 
	ld (0702bh),a		;c971	32 2b 70 	2 + p 
	ld a,(07035h)		;c974	3a 35 70 	: 5 p 
	and 0c0h		;c977	e6 c0 	. . 
	or 004h		;c979	f6 04 	. . 
	ld (07035h),a		;c97b	32 35 70 	2 5 p 
	ret			;c97e	c9 	. 
	ld a,0ffh		;c97f	3e ff 	> . 
	ld (0703fh),a		;c981	32 3f 70 	2 ? p 
	ret			;c984	c9 	. 
	ld b,005h		;c985	06 05 	. . 
	jp 01ff1h		;c987	c3 f1 1f 	. . . 
	ld a,0ffh		;c98a	3e ff 	> . 
	ld (07049h),a		;c98c	32 49 70 	2 I p 
	ld (07053h),a		;c98f	32 53 70 	2 S p 
	ret			;c992	c9 	. 
	ld b,006h		;c993	06 06 	. . 
	call 01ff1h		;c995	cd f1 1f 	. . . 
	ld a,(07053h)		;c998	3a 53 70 	: S p 
	cp 0ffh		;c99b	fe ff 	. . 
	ret nz			;c99d	c0 	. 
	ld b,007h		;c99e	06 07 	. . 
	jp 01ff1h		;c9a0	c3 f1 1f 	. . . 
	ld a,(07053h)		;c9a3	3a 53 70 	: S p 
	and 03fh		;c9a6	e6 3f 	. ? 
	cp 007h		;c9a8	fe 07 	. . 
	jr nz,$+7		;c9aa	20 05 	  . 
	ld a,0ffh		;c9ac	3e ff 	> . 
	ld (07053h),a		;c9ae	32 53 70 	2 S p 
	ld b,008h		;c9b1	06 08 	. . 
	jp 01ff1h		;c9b3	c3 f1 1f 	. . . 
	ld b,009h		;c9b6	06 09 	. . 
	jp 01ff1h		;c9b8	c3 f1 1f 	. . . 
	ld b,00ah		;c9bb	06 0a 	. . 
	jp 01ff1h		;c9bd	c3 f1 1f 	. . . 
	ld b,00bh		;c9c0	06 0b 	. . 
	call 01ff1h		;c9c2	cd f1 1f 	. . . 
	ld a,(07053h)		;c9c5	3a 53 70 	: S p 
	and 03fh		;c9c8	e6 3f 	. ? 
	cp 007h		;c9ca	fe 07 	. . 
	ret z			;c9cc	c8 	. 
	ld b,00ch		;c9cd	06 0c 	. . 
	jp 01ff1h		;c9cf	c3 f1 1f 	. . . 
	ld b,00dh		;c9d2	06 0d 	. . 
	call 01ff1h		;c9d4	cd f1 1f 	. . . 
	ld b,00eh		;c9d7	06 0e 	. . 
	call 01ff1h		;c9d9	cd f1 1f 	. . . 
	ld b,00fh		;c9dc	06 0f 	. . 
	jp 0d3deh		;c9de	c3 de d3 	. . . 
	call 0c958h		;c9e1	cd 58 c9 	. X . 
	ld b,010h		;c9e4	06 10 	. . 
	jp 01ff1h		;c9e6	c3 f1 1f 	. . . 
	ld b,011h		;c9e9	06 11 	. . 
	call 01ff1h		;c9eb	cd f1 1f 	. . . 
	ld b,012h		;c9ee	06 12 	. . 
	jp 01ff1h		;c9f0	c3 f1 1f 	. . . 
	call 0c958h		;c9f3	cd 58 c9 	. X . 
	ld b,013h		;c9f6	06 13 	. . 
	call 01ff1h		;c9f8	cd f1 1f 	. . . 
	ld b,014h		;c9fb	06 14 	. . 
	jp 01ff1h		;c9fd	c3 f1 1f 	. . . 
	ld b,015h		;ca00	06 15 	. . 
	call 01ff1h		;ca02	cd f1 1f 	. . . 
	ld b,016h		;ca05	06 16 	. . 
	jp 01ff1h		;ca07	c3 f1 1f 	. . . 
	call 0c958h		;ca0a	cd 58 c9 	. X . 
	ld b,017h		;ca0d	06 17 	. . 
	call 01ff1h		;ca0f	cd f1 1f 	. . . 
	ld b,018h		;ca12	06 18 	. . 
	jp 01ff1h		;ca14	c3 f1 1f 	. . . 
	call 0c958h		;ca17	cd 58 c9 	. X . 
	ld b,019h		;ca1a	06 19 	. . 
	call 01ff1h		;ca1c	cd f1 1f 	. . . 
	ld b,01ah		;ca1f	06 1a 	. . 
	jp 01ff1h		;ca21	c3 f1 1f 	. . . 
	ld a,0ffh		;ca24	3e ff 	> . 
	ld (07067h),a		;ca26	32 67 70 	2 g p 
	ld (07071h),a		;ca29	32 71 70 	2 q p 
	ret			;ca2c	c9 	. 
	ld a,0ffh		;ca2d	3e ff 	> . 
	ld (07071h),a		;ca2f	32 71 70 	2 q p 
	ld (0707bh),a		;ca32	32 7b 70 	2 { p 
	ret			;ca35	c9 	. 
	ld b,01bh		;ca36	06 1b 	. . 
	call 01ff1h		;ca38	cd f1 1f 	. . . 
	ld b,01ch		;ca3b	06 1c 	. . 
	jp 0d3eah		;ca3d	c3 ea d3 	. . . 
	sub h			;ca40	94 	. 
	call 0702bh		;ca41	cd 2b 70 	. + p 
	push de			;ca44	d5 	. 
	call 0702bh		;ca45	cd 2b 70 	. + p 
	ld c,(hl)			;ca48	4e 	N 
	adc a,035h		;ca49	ce 35 	. 5 
	ld (hl),b			;ca4b	70 	p 
	sub h			;ca4c	94 	. 
	adc a,035h		;ca4d	ce 35 	. 5 
	ld (hl),b			;ca4f	70 	p 
	or b			;ca50	b0 	. 
	jp z,0703fh		;ca51	ca 3f 70 	. ? p 
	ld c,b			;ca54	48 	H 
	bit 1,c		;ca55	cb 49 	. I 
	ld (hl),b			;ca57	70 	p 
	ld c,a			;ca58	4f 	O 
	bit 2,e		;ca59	cb 53 	. S 
	ld (hl),b			;ca5b	70 	p 
	ld d,(hl)			;ca5c	56 	V 
	bit 1,c		;ca5d	cb 49 	. I 
	ld (hl),b			;ca5f	70 	p 
	sub a			;ca60	97 	. 
	bit 1,c		;ca61	cb 49 	. I 
	ld (hl),b			;ca63	70 	p 
	ret c			;ca64	d8 	. 
	bit 3,l		;ca65	cb 5d 	. ] 
	ld (hl),b			;ca67	70 	p 
	pop af			;ca68	f1 	. 
	bit 3,l		;ca69	cb 5d 	. ] 
	ld (hl),b			;ca6b	70 	p 
	defb 0fdh,0cbh,053h,070h	;bit 6,(iy+053h) & ld b,(iy+053h)		;ca6c	fd cb 53 70 	. . S p 
	add hl,bc			;ca70	09 	. 
	call z,0707bh		;ca71	cc 7b 70 	. { p 
	xor b			;ca74	a8 	. 
	call z,07067h		;ca75	cc 67 70 	. g p 
	ld (071cdh),hl		;ca78	22 cd 71 	" . q 
	ld (hl),b			;ca7b	70 	p 
	adc a,l			;ca7c	8d 	. 
	call 0707bh		;ca7d	cd 7b 70 	. { p 
	inc c			;ca80	0c 	. 
	rst 8			;ca81	cf 	. 
	ld h,a			;ca82	67 	g 
	ld (hl),b			;ca83	70 	p 
	and a			;ca84	a7 	. 
	rst 8			;ca85	cf 	. 
	ld (hl),c			;ca86	71 	q 
	ld (hl),b			;ca87	70 	p 
	ld b,d			;ca88	42 	B 
	ret nc			;ca89	d0 	. 
	dec hl			;ca8a	2b 	+ 
	ld (hl),b			;ca8b	70 	p 
	sub c			;ca8c	91 	. 
	ret nc			;ca8d	d0 	. 
	dec (hl)			;ca8e	35 	5 
	ld (hl),b			;ca8f	70 	p 
	ret po			;ca90	e0 	. 
	ret nc			;ca91	d0 	. 
	dec hl			;ca92	2b 	+ 
	ld (hl),b			;ca93	70 	p 
	ld e,c			;ca94	59 	Y 
	pop de			;ca95	d1 	. 
	dec (hl)			;ca96	35 	5 
	ld (hl),b			;ca97	70 	p 
	cp d			;ca98	ba 	. 
	pop de			;ca99	d1 	. 
	dec hl			;ca9a	2b 	+ 
	ld (hl),b			;ca9b	70 	p 
	inc c			;ca9c	0c 	. 
	jp nc,07035h		;ca9d	d2 35 70 	. 5 p 
	inc sp			;caa0	33 	3 
	call 0702bh		;caa1	cd 2b 70 	. + p 
	ld h,b			;caa4	60 	` 
	call 07035h		;caa5	cd 35 70 	. 5 p 
	xor l			;caa8	ad 	. 
	jp nc,07071h		;caa9	d2 71 70 	. q p 
	or l			;caac	b5 	. 
	jp nc,0707bh		;caad	d2 7b 70 	. { p 
	pop bc			;cab0	c1 	. 
	sub 030h		;cab1	d6 30 	. 0 
	ld (bc),a			;cab3	02 	. 
	inc sp			;cab4	33 	3 
	sub l			;cab5	95 	. 
	pop bc			;cab6	c1 	. 
	sub 030h		;cab7	d6 30 	. 0 
	ld (bc),a			;cab9	02 	. 
	inc sp			;caba	33 	3 
	sub l			;cabb	95 	. 
	pop bc			;cabc	c1 	. 
	sub 030h		;cabd	d6 30 	. 0 
	ld (bc),a			;cabf	02 	. 
	inc sp			;cac0	33 	3 
	sub l			;cac1	95 	. 
	jp pe,0bec1h		;cac2	ea c1 be 	. . . 
	jr nc,$+4		;cac5	30 02 	0 . 
	inc sp			;cac7	33 	3 
	and c			;cac8	a1 	. 
	pop bc			;cac9	c1 	. 
	cp (hl)			;caca	be 	. 
	jr nc,$+4		;cacb	30 02 	0 . 
	inc sp			;cacd	33 	3 
	and c			;cace	a1 	. 
	pop bc			;cacf	c1 	. 
	cp (hl)			;cad0	be 	. 
	jr nc,$+4		;cad1	30 02 	0 . 
	inc sp			;cad3	33 	3 
	and c			;cad4	a1 	. 
	jp pe,0aac1h		;cad5	ea c1 aa 	. . . 
	jr nc,$+4		;cad8	30 02 	0 . 
	inc sp			;cada	33 	3 
	xor e			;cadb	ab 	. 
	pop bc			;cadc	c1 	. 
	xor d			;cadd	aa 	. 
	jr nc,$+4		;cade	30 02 	0 . 
	inc sp			;cae0	33 	3 
	xor e			;cae1	ab 	. 
	pop bc			;cae2	c1 	. 
	xor d			;cae3	aa 	. 
	jr nc,$+4		;cae4	30 02 	0 . 
	inc sp			;cae6	33 	3 
	xor e			;cae7	ab 	. 
	jp pe,0a0c1h		;cae8	ea c1 a0 	. . . 
	jr nc,$+4		;caeb	30 02 	0 . 
	inc sp			;caed	33 	3 
	or b			;caee	b0 	. 
	pop bc			;caef	c1 	. 
	and b			;caf0	a0 	. 
	jr nc,$+4		;caf1	30 02 	0 . 
	inc sp			;caf3	33 	3 
	or b			;caf4	b0 	. 
	pop bc			;caf5	c1 	. 
	and b			;caf6	a0 	. 
	jr nc,$+4		;caf7	30 02 	0 . 
	inc sp			;caf9	33 	3 
	or b			;cafa	b0 	. 
	jp pe,08fc1h		;cafb	ea c1 8f 	. . . 
	jr nc,$+4		;cafe	30 02 	0 . 
	inc sp			;cb00	33 	3 
	cp c			;cb01	b9 	. 
	pop bc			;cb02	c1 	. 
	adc a,a			;cb03	8f 	. 
	jr nc,$+4		;cb04	30 02 	0 . 
	inc sp			;cb06	33 	3 
	cp c			;cb07	b9 	. 
	pop bc			;cb08	c1 	. 
	adc a,a			;cb09	8f 	. 
	jr nc,$+4		;cb0a	30 02 	0 . 
	inc sp			;cb0c	33 	3 
	cp c			;cb0d	b9 	. 
	jp pe,07fc1h		;cb0e	ea c1 7f 	. .  
	jr nc,$+4		;cb11	30 02 	0 . 
	inc sp			;cb13	33 	3 
	pop bc			;cb14	c1 	. 
	pop bc			;cb15	c1 	. 
	ld a,a			;cb16	7f 	 
	jr nc,$+4		;cb17	30 02 	0 . 
	inc sp			;cb19	33 	3 
	pop bc			;cb1a	c1 	. 
	pop bc			;cb1b	c1 	. 
	ld a,a			;cb1c	7f 	 
	jr nc,$+4		;cb1d	30 02 	0 . 
	inc sp			;cb1f	33 	3 
	pop bc			;cb20	c1 	. 
	jp pe,071c1h		;cb21	ea c1 71 	. . q 
	jr nc,$+4		;cb24	30 02 	0 . 
	inc sp			;cb26	33 	3 
	ret z			;cb27	c8 	. 
	pop bc			;cb28	c1 	. 
	ld (hl),c			;cb29	71 	q 
	jr nc,$+4		;cb2a	30 02 	0 . 
	inc sp			;cb2c	33 	3 
	ret z			;cb2d	c8 	. 
	pop bc			;cb2e	c1 	. 
	ld (hl),c			;cb2f	71 	q 
	jr nc,$+4		;cb30	30 02 	0 . 
	inc sp			;cb32	33 	3 
	ret z			;cb33	c8 	. 
	jp pe,06bc1h		;cb34	ea c1 6b 	. . k 
	jr nc,$+4		;cb37	30 02 	0 . 
	inc sp			;cb39	33 	3 
	set 0,c		;cb3a	cb c1 	. . 
	ld l,e			;cb3c	6b 	k 
	jr nc,$+4		;cb3d	30 02 	0 . 
	inc sp			;cb3f	33 	3 
	set 0,c		;cb40	cb c1 	. . 
	ld l,e			;cb42	6b 	k 
	jr nc,$+4		;cb43	30 02 	0 . 
	inc sp			;cb45	33 	3 
	set 2,b		;cb46	cb d0 	. . 
	add a,d			;cb48	82 	. 
	ld c,e			;cb49	4b 	K 
	add a,c			;cb4a	81 	. 
	ld b,0c2h		;cb4b	06 c2 	. . 
	inc sp			;cb4d	33 	3 
	sbc a,b			;cb4e	98 	. 
	jp nz,0818ah		;cb4f	c2 8a 81 	. . . 
	ld b,0c2h		;cb52	06 c2 	. . 
	inc sp			;cb54	33 	3 
	ret c			;cb55	d8 	. 
	ret nz			;cb56	c0 	. 
	ld b,b			;cb57	40 	@ 
	ld bc,0c103h		;cb58	01 03 c1 	. . . 
	ld a,a			;cb5b	7f 	 
	djnz $+4		;cb5c	10 02 	. . 
	inc sp			;cb5e	33 	3 
	ld a,a			;cb5f	7f 	 
	pop bc			;cb60	c1 	. 
	ld l,e			;cb61	6b 	k 
	djnz $+4		;cb62	10 02 	. . 
	inc sp			;cb64	33 	3 
	ld l,e			;cb65	6b 	k 
	pop bc			;cb66	c1 	. 
	ld d,b			;cb67	50 	P 
	jr nz,$+4		;cb68	20 02 	  . 
	inc sp			;cb6a	33 	3 
	ld d,b			;cb6b	50 	P 
	pop bc			;cb6c	c1 	. 
	ld b,b			;cb6d	40 	@ 
	jr nz,$+4		;cb6e	20 02 	  . 
	inc sp			;cb70	33 	3 
	ld b,b			;cb71	40 	@ 
	pop bc			;cb72	c1 	. 
	dec (hl)			;cb73	35 	5 
	jr nc,$+4		;cb74	30 02 	0 . 
	inc sp			;cb76	33 	3 
	dec (hl)			;cb77	35 	5 
	pop bc			;cb78	c1 	. 
	jr z,$+66		;cb79	28 40 	( @ 
	ld (bc),a			;cb7b	02 	. 
	inc sp			;cb7c	33 	3 
	jr z,$-61		;cb7d	28 c1 	( . 
	jr nz,$+82		;cb7f	20 50 	  P 
	ld (bc),a			;cb81	02 	. 
	inc sp			;cb82	33 	3 
	jr nz,$-61		;cb83	20 c1 	  . 
	jr $+98		;cb85	18 60 	. ` 
	ld (bc),a			;cb87	02 	. 
	inc sp			;cb88	33 	3 
	jr $-61		;cb89	18 c1 	. . 
	inc d			;cb8b	14 	. 
	ld (hl),b			;cb8c	70 	p 
	ld (bc),a			;cb8d	02 	. 
	inc sp			;cb8e	33 	3 
	inc d			;cb8f	14 	. 
	pop bc			;cb90	c1 	. 
	djnz $-126		;cb91	10 80 	. . 
	ld (bc),a			;cb93	02 	. 
	inc sp			;cb94	33 	3 
	djnz $-46		;cb95	10 d0 	. . 
	pop bc			;cb97	c1 	. 
	djnz $-126		;cb98	10 80 	. . 
	ld (bc),a			;cb9a	02 	. 
	inc sp			;cb9b	33 	3 
	djnz $-61		;cb9c	10 c1 	. . 
	inc d			;cb9e	14 	. 
	ld (hl),b			;cb9f	70 	p 
	ld (bc),a			;cba0	02 	. 
	inc sp			;cba1	33 	3 
	inc d			;cba2	14 	. 
	pop bc			;cba3	c1 	. 
	jr $+98		;cba4	18 60 	. ` 
	ld (bc),a			;cba6	02 	. 
	inc sp			;cba7	33 	3 
	jr $-61		;cba8	18 c1 	. . 
	jr nz,$+82		;cbaa	20 50 	  P 
	ld (bc),a			;cbac	02 	. 
	inc sp			;cbad	33 	3 
	jr nz,$-61		;cbae	20 c1 	  . 
	jr z,$+82		;cbb0	28 50 	( P 
	ld (bc),a			;cbb2	02 	. 
	inc sp			;cbb3	33 	3 
	jr z,$-61		;cbb4	28 c1 	( . 
	dec (hl)			;cbb6	35 	5 
	ld b,b			;cbb7	40 	@ 
	ld (bc),a			;cbb8	02 	. 
	inc sp			;cbb9	33 	3 
	dec (hl)			;cbba	35 	5 
	pop bc			;cbbb	c1 	. 
	ld b,b			;cbbc	40 	@ 
	ld b,b			;cbbd	40 	@ 
	ld (bc),a			;cbbe	02 	. 
	inc sp			;cbbf	33 	3 
	ld b,b			;cbc0	40 	@ 
	pop bc			;cbc1	c1 	. 
	ld d,b			;cbc2	50 	P 
	jr nc,$+4		;cbc3	30 02 	0 . 
	inc sp			;cbc5	33 	3 
	ld d,b			;cbc6	50 	P 
	pop bc			;cbc7	c1 	. 
	ld l,e			;cbc8	6b 	k 
	jr nc,$+4		;cbc9	30 02 	0 . 
	inc sp			;cbcb	33 	3 
	ld l,e			;cbcc	6b 	k 
	pop bc			;cbcd	c1 	. 
	ld a,a			;cbce	7f 	 
	jr nz,$+4		;cbcf	20 02 	  . 
	inc sp			;cbd1	33 	3 
	ld a,a			;cbd2	7f 	 
	ret nz			;cbd3	c0 	. 
	ld b,b			;cbd4	40 	@ 
	ld de,0d003h		;cbd5	11 03 d0 	. . . 
	add a,c			;cbd8	81 	. 
	add hl,sp			;cbd9	39 	9 
	ld d,b			;cbda	50 	P 
	rlca			;cbdb	07 	. 
	ld b,h			;cbdc	44 	D 
	inc b			;cbdd	04 	. 
	add a,c			;cbde	81 	. 
	ld e,c			;cbdf	59 	Y 
	jr nc,$+9		;cbe0	30 07 	0 . 
	ld b,h			;cbe2	44 	D 
	rlca			;cbe3	07 	. 
	add a,c			;cbe4	81 	. 
	sub c			;cbe5	91 	. 
	ld (hl),b			;cbe6	70 	p 
	rlca			;cbe7	07 	. 
	ld b,h			;cbe8	44 	D 
	dec bc			;cbe9	0b 	. 
	add a,c			;cbea	81 	. 
	jp (hl)			;cbeb	e9 	. 
	or b			;cbec	b0 	. 
	rlca			;cbed	07 	. 
	ld b,h			;cbee	44 	D 
	djnz $-110		;cbef	10 90 	. . 
	add a,b			;cbf1	80 	. 
	xor h			;cbf2	ac 	. 
	ld de,0a708h		;cbf3	11 08 a7 	. . . 
	add a,c			;cbf6	81 	. 
	ld l,e			;cbf7	6b 	k 
	jr nc,$+4		;cbf8	30 02 	0 . 
	ld b,a			;cbfa	47 	G 
	jp m,0c090h		;cbfb	fa 90 c0 	. . . 
	dec e			;cbfe	1d 	. 
	ld de,0e708h		;cbff	11 08 e7 	. . . 
	pop bc			;cc02	c1 	. 
	ld a,a			;cc03	7f 	 
	jr nc,$+4		;cc04	30 02 	0 . 
	ld b,a			;cc06	47 	G 
	ld sp,hl			;cc07	f9 	. 
	ret nc			;cc08	d0 	. 
	ld b,c			;cc09	41 	A 
	dec de			;cc0a	1b 	. 
	nop			;cc0b	00 	. 
	ld (bc),a			;cc0c	02 	. 
	ld h,(hl)			;cc0d	66 	f 
	ld bc,02041h		;cc0e	01 41 20 	. A   
	jr nz,$+4		;cc11	20 02 	  . 
	ld h,(hl)			;cc13	66 	f 
	inc b			;cc14	04 	. 
	ld b,b			;cc15	40 	@ 
	jr z,$+50		;cc16	28 30 	( 0 
	ld b,06fh		;cc18	06 6f 	. o 
	ld b,b			;cc1a	40 	@ 
	ld l,e			;cc1b	6b 	k 
	jr nc,$+9		;cc1c	30 07 	0 . 
	ld h,e			;cc1e	63 	c 
	ld b,b			;cc1f	40 	@ 
	ld l,e			;cc20	6b 	k 
	jr nc,$+9		;cc21	30 07 	0 . 
	ld h,e			;cc23	63 	c 
	ld b,b			;cc24	40 	@ 
	ld d,l			;cc25	55 	U 
	jr nc,$+9		;cc26	30 07 	0 . 
	ld h,e			;cc28	63 	c 
	ld b,b			;cc29	40 	@ 
	ld d,l			;cc2a	55 	U 
	jr nc,$+9		;cc2b	30 07 	0 . 
	ld h,e			;cc2d	63 	c 
	ld b,b			;cc2e	40 	@ 
	ld b,a			;cc2f	47 	G 
	jr nc,$+9		;cc30	30 07 	0 . 
	ld h,e			;cc32	63 	c 
	ld b,b			;cc33	40 	@ 
	ld b,a			;cc34	47 	G 
	jr nc,$+9		;cc35	30 07 	0 . 
	ld h,e			;cc37	63 	c 
	ld b,b			;cc38	40 	@ 
	ld d,l			;cc39	55 	U 
	jr nc,$+12		;cc3a	30 0a 	0 . 
	ld l,d			;cc3c	6a 	j 
	ld b,b			;cc3d	40 	@ 
	ld d,b			;cc3e	50 	P 
	jr nc,$+9		;cc3f	30 07 	0 . 
	ld h,e			;cc41	63 	c 
	ld b,b			;cc42	40 	@ 
	ld d,b			;cc43	50 	P 
	jr nc,$+9		;cc44	30 07 	0 . 
	ld h,e			;cc46	63 	c 
	ld b,b			;cc47	40 	@ 
	ld e,a			;cc48	5f 	_ 
	jr nc,$+9		;cc49	30 07 	0 . 
	ld h,e			;cc4b	63 	c 
	ld b,b			;cc4c	40 	@ 
	ld e,a			;cc4d	5f 	_ 
	jr nc,$+9		;cc4e	30 07 	0 . 
	ld h,e			;cc50	63 	c 
	ld b,b			;cc51	40 	@ 
	ld (hl),c			;cc52	71 	q 
	jr nc,$+9		;cc53	30 07 	0 . 
	ld h,e			;cc55	63 	c 
	ld b,b			;cc56	40 	@ 
	ld (hl),c			;cc57	71 	q 
	jr nc,$+9		;cc58	30 07 	0 . 
	ld h,e			;cc5a	63 	c 
	ld b,b			;cc5b	40 	@ 
	adc a,a			;cc5c	8f 	. 
	jr nc,$+12		;cc5d	30 0a 	0 . 
	ld l,d			;cc5f	6a 	j 
	ld b,b			;cc60	40 	@ 
	xor d			;cc61	aa 	. 
	ld b,b			;cc62	40 	@ 
	rlca			;cc63	07 	. 
	ld h,e			;cc64	63 	c 
	ld b,b			;cc65	40 	@ 
	xor d			;cc66	aa 	. 
	ld b,b			;cc67	40 	@ 
	rlca			;cc68	07 	. 
	ld h,e			;cc69	63 	c 
	ld b,b			;cc6a	40 	@ 
	adc a,a			;cc6b	8f 	. 
	ld b,b			;cc6c	40 	@ 
	rlca			;cc6d	07 	. 
	ld h,e			;cc6e	63 	c 
	ld b,b			;cc6f	40 	@ 
	adc a,a			;cc70	8f 	. 
	ld b,b			;cc71	40 	@ 
	rlca			;cc72	07 	. 
	ld h,e			;cc73	63 	c 
	ld b,b			;cc74	40 	@ 
	ld l,e			;cc75	6b 	k 
	ld b,b			;cc76	40 	@ 
	rlca			;cc77	07 	. 
	ld h,e			;cc78	63 	c 
	ld b,b			;cc79	40 	@ 
	ld l,e			;cc7a	6b 	k 
	ld b,b			;cc7b	40 	@ 
	rlca			;cc7c	07 	. 
	ld h,e			;cc7d	63 	c 
	ld b,b			;cc7e	40 	@ 
	ld d,l			;cc7f	55 	U 
	ld b,b			;cc80	40 	@ 
	ld a,(bc)			;cc81	0a 	. 
	ld l,d			;cc82	6a 	j 
	ld b,b			;cc83	40 	@ 
	ld e,a			;cc84	5f 	_ 
	ld b,b			;cc85	40 	@ 
	rlca			;cc86	07 	. 
	ld h,e			;cc87	63 	c 
	ld b,b			;cc88	40 	@ 
	ld e,a			;cc89	5f 	_ 
	ld b,b			;cc8a	40 	@ 
	rlca			;cc8b	07 	. 
	ld h,e			;cc8c	63 	c 
	ld b,c			;cc8d	41 	A 
	ld l,e			;cc8e	6b 	k 
	ld b,b			;cc8f	40 	@ 
	ld (bc),a			;cc90	02 	. 
	ld d,l			;cc91	55 	U 
	ld b,041h		;cc92	06 41 	. A 
	ld a,a			;cc94	7f 	 
	ld b,b			;cc95	40 	@ 
	ld (bc),a			;cc96	02 	. 
	ld d,l			;cc97	55 	U 
	jp p,06b40h		;cc98	f2 40 6b 	. @ k 
	ld b,b			;cc9b	40 	@ 
	rlca			;cc9c	07 	. 
	ld h,e			;cc9d	63 	c 
	ld b,b			;cc9e	40 	@ 
	ld l,e			;cc9f	6b 	k 
	ld b,b			;cca0	40 	@ 
	rlca			;cca1	07 	. 
	ld h,e			;cca2	63 	c 
	ld b,b			;cca3	40 	@ 
	ld l,e			;cca4	6b 	k 
	ld b,b			;cca5	40 	@ 
	ld a,(bc)			;cca6	0a 	. 
	ld d,b			;cca7	50 	P 
	add a,c			;cca8	81 	. 
	inc a			;cca9	3c 	< 
	nop			;ccaa	00 	. 
	ld (bc),a			;ccab	02 	. 
	ld h,(hl)			;ccac	66 	f 
	djnz $-126		;ccad	10 80 	. . 
	ld (00620h),a		;ccaf	32 20 06 	2   . 
	add a,c			;ccb2	81 	. 
	ld h,l			;ccb3	65 	e 
	jr nc,$+4		;ccb4	30 02 	0 . 
	ld h,(hl)			;ccb6	66 	f 
	rst 20h			;ccb7	e7 	. 
	xor a			;ccb8	af 	. 
	add a,b			;ccb9	80 	. 
	sub 040h		;ccba	d6 40 	. @ 
	rlca			;ccbc	07 	. 
	and e			;ccbd	a3 	. 
	add a,b			;ccbe	80 	. 
	xor d			;ccbf	aa 	. 
	ld b,b			;ccc0	40 	@ 
	ld a,(bc)			;ccc1	0a 	. 
	xor d			;ccc2	aa 	. 
	add a,b			;ccc3	80 	. 
	adc a,a			;ccc4	8f 	. 
	ld b,b			;ccc5	40 	@ 
	rlca			;ccc6	07 	. 
	and e			;ccc7	a3 	. 
	add a,b			;ccc8	80 	. 
	xor d			;ccc9	aa 	. 
	ld b,b			;ccca	40 	@ 
	ld a,(bc)			;cccb	0a 	. 
	xor d			;cccc	aa 	. 
	add a,b			;cccd	80 	. 
	ld a,a			;ccce	7f 	 
	ld b,b			;cccf	40 	@ 
	ld a,(bc)			;ccd0	0a 	. 
	xor d			;ccd1	aa 	. 
	add a,b			;ccd2	80 	. 
	adc a,a			;ccd3	8f 	. 
	ld b,b			;ccd4	40 	@ 
	rlca			;ccd5	07 	. 
	and e			;ccd6	a3 	. 
	add a,b			;ccd7	80 	. 
	ld (hl),c			;ccd8	71 	q 
	ld b,b			;ccd9	40 	@ 
	ld a,(bc)			;ccda	0a 	. 
	xor d			;ccdb	aa 	. 
	add a,b			;ccdc	80 	. 
	ld e,a			;ccdd	5f 	_ 
	ld b,b			;ccde	40 	@ 
	rlca			;ccdf	07 	. 
	and e			;cce0	a3 	. 
	add a,b			;cce1	80 	. 
	ld b,a			;cce2	47 	G 
	ld b,b			;cce3	40 	@ 
	inc d			;cce4	14 	. 
	or h			;cce5	b4 	. 
	add a,b			;cce6	80 	. 
	ld b,a			;cce7	47 	G 
	jr nc,$+9		;cce8	30 07 	0 . 
	and e			;ccea	a3 	. 
	add a,b			;cceb	80 	. 
	ld b,b			;ccec	40 	@ 
	jr nc,$+9		;cced	30 07 	0 . 
	and e			;ccef	a3 	. 
	add a,b			;ccf0	80 	. 
	ld b,a			;ccf1	47 	G 
	jr nc,$+9		;ccf2	30 07 	0 . 
	and e			;ccf4	a3 	. 
	add a,b			;ccf5	80 	. 
	ld b,b			;ccf6	40 	@ 
	jr nc,$+9		;ccf7	30 07 	0 . 
	and e			;ccf9	a3 	. 
	add a,b			;ccfa	80 	. 
	ld b,a			;ccfb	47 	G 
	jr nc,$+9		;ccfc	30 07 	0 . 
	and e			;ccfe	a3 	. 
	add a,b			;ccff	80 	. 
	ld b,a			;cd00	47 	G 
	jr nc,$+9		;cd01	30 07 	0 . 
	and e			;cd03	a3 	. 
	add a,b			;cd04	80 	. 
	ld d,l			;cd05	55 	U 
	jr nc,$+12		;cd06	30 0a 	0 . 
	xor d			;cd08	aa 	. 
	add a,b			;cd09	80 	. 
	ld d,b			;cd0a	50 	P 
	jr nc,$+9		;cd0b	30 07 	0 . 
	and e			;cd0d	a3 	. 
	add a,b			;cd0e	80 	. 
	ld d,b			;cd0f	50 	P 
	jr nc,$+9		;cd10	30 07 	0 . 
	and e			;cd12	a3 	. 
	add a,b			;cd13	80 	. 
	ld e,a			;cd14	5f 	_ 
	jr nc,$+9		;cd15	30 07 	0 . 
	and e			;cd17	a3 	. 
	add a,b			;cd18	80 	. 
	ld e,a			;cd19	5f 	_ 
	jr nc,$+9		;cd1a	30 07 	0 . 
	and e			;cd1c	a3 	. 
	add a,b			;cd1d	80 	. 
	ld l,e			;cd1e	6b 	k 
	jr nc,$+12		;cd1f	30 0a 	0 . 
	sub b			;cd21	90 	. 
	pop bc			;cd22	c1 	. 
	ld b,b			;cd23	40 	@ 
	nop			;cd24	00 	. 
	ld (bc),a			;cd25	02 	. 
	ld h,(hl)			;cd26	66 	f 
	djnz $-62		;cd27	10 c0 	. . 
	dec (hl)			;cd29	35 	5 
	jr nz,$+8		;cd2a	20 06 	  . 
	pop bc			;cd2c	c1 	. 
	ld l,e			;cd2d	6b 	k 
	jr nc,$+4		;cd2e	30 02 	0 . 
	ld h,(hl)			;cd30	66 	f 
	push hl			;cd31	e5 	. 
	ret nc			;cd32	d0 	. 
	ld b,b			;cd33	40 	@ 
	ld l,e			;cd34	6b 	k 
	jr nc,$+6		;cd35	30 04 	0 . 
	ld h,d			;cd37	62 	b 
	ld b,b			;cd38	40 	@ 
	ld a,b			;cd39	78 	x 
	jr nc,$+6		;cd3a	30 04 	0 . 
	ld h,d			;cd3c	62 	b 
	ld b,b			;cd3d	40 	@ 
	add a,a			;cd3e	87 	. 
	jr nc,$+6		;cd3f	30 04 	0 . 
	ld h,d			;cd41	62 	b 
	ld b,b			;cd42	40 	@ 
	sub a			;cd43	97 	. 
	jr nc,$+6		;cd44	30 04 	0 . 
	ld h,d			;cd46	62 	b 
	ld b,b			;cd47	40 	@ 
	xor d			;cd48	aa 	. 
	jr nc,$+6		;cd49	30 04 	0 . 
	ld h,d			;cd4b	62 	b 
	ld b,b			;cd4c	40 	@ 
	cp (hl)			;cd4d	be 	. 
	jr nc,$+6		;cd4e	30 04 	0 . 
	ld h,d			;cd50	62 	b 
	ld b,b			;cd51	40 	@ 
	sub 030h		;cd52	d6 30 	. 0 
	inc b			;cd54	04 	. 
	ld l,d			;cd55	6a 	j 
	ld b,b			;cd56	40 	@ 
	adc a,a			;cd57	8f 	. 
	jr nc,$+6		;cd58	30 04 	0 . 
	ld l,d			;cd5a	6a 	j 
	ld b,b			;cd5b	40 	@ 
	ld l,e			;cd5c	6b 	k 
	jr nc,$+6		;cd5d	30 04 	0 . 
	ld d,b			;cd5f	50 	P 
	add a,b			;cd60	80 	. 
	ld l,b			;cd61	68 	h 
	ld sp,0a204h		;cd62	31 04 a2 	1 . . 
	add a,b			;cd65	80 	. 
	ld d,e			;cd66	53 	S 
	ld sp,0a204h		;cd67	31 04 a2 	1 . . 
	add a,b			;cd6a	80 	. 
	ld b,b			;cd6b	40 	@ 
	ld sp,0a204h		;cd6c	31 04 a2 	1 . . 
	add a,b			;cd6f	80 	. 
	ret p			;cd70	f0 	. 
	jr nc,$+6		;cd71	30 04 	0 . 
	and d			;cd73	a2 	. 
	add a,b			;cd74	80 	. 
	jp po,00430h		;cd75	e2 30 04 	. 0 . 
	and d			;cd78	a2 	. 
	add a,b			;cd79	80 	. 
	and b			;cd7a	a0 	. 
	jr nc,$+6		;cd7b	30 04 	0 . 
	and d			;cd7d	a2 	. 
	add a,b			;cd7e	80 	. 
	xor d			;cd7f	aa 	. 
	jr nc,$+6		;cd80	30 04 	0 . 
	xor d			;cd82	aa 	. 
	add a,b			;cd83	80 	. 
	dec e			;cd84	1d 	. 
	ld sp,0aa04h		;cd85	31 04 aa 	1 . . 
	add a,b			;cd88	80 	. 
	xor h			;cd89	ac 	. 
	ld sp,09004h		;cd8a	31 04 90 	1 . . 
	add a,d			;cd8d	82 	. 
	rla			;cd8e	17 	. 
	ld d,b			;cd8f	50 	P 
	ex af,af'			;cd90	08 	. 
	dec de			;cd91	1b 	. 
	ld de,04098h		;cd92	11 98 40 	. . @ 
	adc a,a			;cd95	8f 	. 
	ld h,b			;cd96	60 	` 
	rlca			;cd97	07 	. 
	ld h,e			;cd98	63 	c 
	ld b,b			;cd99	40 	@ 
	sub 060h		;cd9a	d6 60 	. ` 
	rlca			;cd9c	07 	. 
	ld h,e			;cd9d	63 	c 
	ld b,b			;cd9e	40 	@ 
	sub 060h		;cd9f	d6 60 	. ` 
	rlca			;cda1	07 	. 
	ld h,e			;cda2	63 	c 
	ld b,b			;cda3	40 	@ 
	sub 060h		;cda4	d6 60 	. ` 
	rlca			;cda6	07 	. 
	ld h,e			;cda7	63 	c 
	ld b,b			;cda8	40 	@ 
	and b			;cda9	a0 	. 
	ld h,b			;cdaa	60 	` 
	rlca			;cdab	07 	. 
	ld h,e			;cdac	63 	c 
	ld b,b			;cdad	40 	@ 
	jp po,00760h		;cdae	e2 60 07 	. ` . 
	ld h,e			;cdb1	63 	c 
	ld b,b			;cdb2	40 	@ 
	jp po,00760h		;cdb3	e2 60 07 	. ` . 
	ld h,e			;cdb6	63 	c 
	ld b,b			;cdb7	40 	@ 
	jp po,00760h		;cdb8	e2 60 07 	. ` . 
	ld h,e			;cdbb	63 	c 
	ld b,b			;cdbc	40 	@ 
	adc a,a			;cdbd	8f 	. 
	ld h,b			;cdbe	60 	` 
	rlca			;cdbf	07 	. 
	ld h,e			;cdc0	63 	c 
	ld b,b			;cdc1	40 	@ 
	and b			;cdc2	a0 	. 
	ld h,b			;cdc3	60 	` 
	rlca			;cdc4	07 	. 
	ld h,e			;cdc5	63 	c 
	ld b,b			;cdc6	40 	@ 
	xor d			;cdc7	aa 	. 
	ld h,b			;cdc8	60 	` 
	rlca			;cdc9	07 	. 
	ld h,e			;cdca	63 	c 
	ld b,b			;cdcb	40 	@ 
	cp (hl)			;cdcc	be 	. 
	ld h,b			;cdcd	60 	` 
	rlca			;cdce	07 	. 
	ld h,e			;cdcf	63 	c 
	ld b,b			;cdd0	40 	@ 
	sub 060h		;cdd1	d6 60 	. ` 
	ld e,06ah		;cdd3	1e 6a 	. j 
	ld b,b			;cdd5	40 	@ 
	cp (hl)			;cdd6	be 	. 
	ld h,b			;cdd7	60 	` 
	rlca			;cdd8	07 	. 
	ld h,e			;cdd9	63 	c 
	ld b,b			;cdda	40 	@ 
	xor d			;cddb	aa 	. 
	ld h,b			;cddc	60 	` 
	rlca			;cddd	07 	. 
	ld h,e			;cdde	63 	c 
	ld b,b			;cddf	40 	@ 
	and b			;cde0	a0 	. 
	ld h,b			;cde1	60 	` 
	rlca			;cde2	07 	. 
	ld h,e			;cde3	63 	c 
	ld b,b			;cde4	40 	@ 
	adc a,a			;cde5	8f 	. 
	ld h,b			;cde6	60 	` 
	rlca			;cde7	07 	. 
	ld h,e			;cde8	63 	c 
	ld b,b			;cde9	40 	@ 
	ld a,a			;cdea	7f 	 
	ld h,b			;cdeb	60 	` 
	ld a,(bc)			;cdec	0a 	. 
	ld l,d			;cded	6a 	j 
	ld b,b			;cdee	40 	@ 
	ld l,e			;cdef	6b 	k 
	ld h,b			;cdf0	60 	` 
	ld a,(bc)			;cdf1	0a 	. 
	ld l,d			;cdf2	6a 	j 
	ld b,b			;cdf3	40 	@ 
	ld (hl),c			;cdf4	71 	q 
	ld h,b			;cdf5	60 	` 
	rlca			;cdf6	07 	. 
	ld h,e			;cdf7	63 	c 
	ld b,b			;cdf8	40 	@ 
	ld (hl),c			;cdf9	71 	q 
	ld h,b			;cdfa	60 	` 
	rlca			;cdfb	07 	. 
	ld h,e			;cdfc	63 	c 
	ld b,b			;cdfd	40 	@ 
	ld a,a			;cdfe	7f 	 
	ld h,b			;cdff	60 	` 
	rlca			;ce00	07 	. 
	ld h,e			;ce01	63 	c 
	ld b,b			;ce02	40 	@ 
	ld (hl),c			;ce03	71 	q 
	ld h,b			;ce04	60 	` 
	rlca			;ce05	07 	. 
	ld h,e			;ce06	63 	c 
	ld b,b			;ce07	40 	@ 
	adc a,a			;ce08	8f 	. 
	ld h,b			;ce09	60 	` 
	ld e,06ah		;ce0a	1e 6a 	. j 
	ld b,b			;ce0c	40 	@ 
	adc a,a			;ce0d	8f 	. 
	ld h,b			;ce0e	60 	` 
	rlca			;ce0f	07 	. 
	ld h,e			;ce10	63 	c 
	ld b,b			;ce11	40 	@ 
	ld l,e			;ce12	6b 	k 
	ld h,b			;ce13	60 	` 
	rlca			;ce14	07 	. 
	ld h,e			;ce15	63 	c 
	ld b,b			;ce16	40 	@ 
	ld (hl),c			;ce17	71 	q 
	ld h,b			;ce18	60 	` 
	rlca			;ce19	07 	. 
	ld h,e			;ce1a	63 	c 
	ld b,b			;ce1b	40 	@ 
	ld a,a			;ce1c	7f 	 
	ld h,b			;ce1d	60 	` 
	rlca			;ce1e	07 	. 
	ld h,e			;ce1f	63 	c 
	ld b,b			;ce20	40 	@ 
	adc a,a			;ce21	8f 	. 
	ld h,b			;ce22	60 	` 
	rlca			;ce23	07 	. 
	ld h,e			;ce24	63 	c 
	ld b,b			;ce25	40 	@ 
	adc a,a			;ce26	8f 	. 
	ld h,b			;ce27	60 	` 
	rlca			;ce28	07 	. 
	ld h,e			;ce29	63 	c 
	ld b,b			;ce2a	40 	@ 
	adc a,a			;ce2b	8f 	. 
	ld h,b			;ce2c	60 	` 
	rlca			;ce2d	07 	. 
	ld h,e			;ce2e	63 	c 
	ld b,b			;ce2f	40 	@ 
	adc a,a			;ce30	8f 	. 
	ld h,b			;ce31	60 	` 
	rlca			;ce32	07 	. 
	ld h,e			;ce33	63 	c 
	ld b,b			;ce34	40 	@ 
	and b			;ce35	a0 	. 
	ld h,b			;ce36	60 	` 
	rlca			;ce37	07 	. 
	ld h,e			;ce38	63 	c 
	ld b,b			;ce39	40 	@ 
	ld a,a			;ce3a	7f 	 
	ld h,b			;ce3b	60 	` 
	rlca			;ce3c	07 	. 
	ld h,e			;ce3d	63 	c 
	ld b,b			;ce3e	40 	@ 
	adc a,a			;ce3f	8f 	. 
	ld h,b			;ce40	60 	` 
	rlca			;ce41	07 	. 
	ld h,e			;ce42	63 	c 
	ld b,b			;ce43	40 	@ 
	and b			;ce44	a0 	. 
	ld h,b			;ce45	60 	` 
	rlca			;ce46	07 	. 
	ld h,e			;ce47	63 	c 
	ld b,b			;ce48	40 	@ 
	xor d			;ce49	aa 	. 
	ld h,b			;ce4a	60 	` 
	ld e,06ah		;ce4b	1e 6a 	. j 
	ld e,b			;ce4d	58 	X 
	add a,b			;ce4e	80 	. 
	xor d			;ce4f	aa 	. 
	add a,b			;ce50	80 	. 
	rlca			;ce51	07 	. 
	and e			;ce52	a3 	. 
	add a,b			;ce53	80 	. 
	xor d			;ce54	aa 	. 
	add a,b			;ce55	80 	. 
	ld a,(bc)			;ce56	0a 	. 
	xor d			;ce57	aa 	. 
	add a,b			;ce58	80 	. 
	xor d			;ce59	aa 	. 
	add a,b			;ce5a	80 	. 
	rlca			;ce5b	07 	. 
	and e			;ce5c	a3 	. 
	add a,b			;ce5d	80 	. 
	cp (hl)			;ce5e	be 	. 
	add a,b			;ce5f	80 	. 
	rlca			;ce60	07 	. 
	and e			;ce61	a3 	. 
	add a,b			;ce62	80 	. 
	cp (hl)			;ce63	be 	. 
	add a,b			;ce64	80 	. 
	ld a,(bc)			;ce65	0a 	. 
	xor d			;ce66	aa 	. 
	add a,b			;ce67	80 	. 
	cp (hl)			;ce68	be 	. 
	add a,b			;ce69	80 	. 
	rlca			;ce6a	07 	. 
	and e			;ce6b	a3 	. 
	add a,b			;ce6c	80 	. 
	xor d			;ce6d	aa 	. 
	add a,b			;ce6e	80 	. 
	rlca			;ce6f	07 	. 
	and e			;ce70	a3 	. 
	add a,b			;ce71	80 	. 
	cp (hl)			;ce72	be 	. 
	add a,b			;ce73	80 	. 
	rlca			;ce74	07 	. 
	and e			;ce75	a3 	. 
	add a,b			;ce76	80 	. 
	sub 080h		;ce77	d6 80 	. . 
	rlca			;ce79	07 	. 
	and e			;ce7a	a3 	. 
	add a,b			;ce7b	80 	. 
	jp po,00780h		;ce7c	e2 80 07 	. . . 
	and e			;ce7f	a3 	. 
	add a,b			;ce80	80 	. 
	sub 080h		;ce81	d6 80 	. . 
	rlca			;ce83	07 	. 
	and e			;ce84	a3 	. 
	add a,b			;ce85	80 	. 
	jp po,00780h		;ce86	e2 80 07 	. . . 
	and e			;ce89	a3 	. 
	add a,b			;ce8a	80 	. 
	cp 080h		;ce8b	fe 80 	. . 
	rlca			;ce8d	07 	. 
	and e			;ce8e	a3 	. 
	add a,b			;ce8f	80 	. 
	dec e			;ce90	1d 	. 
	add a,c			;ce91	81 	. 
	rlca			;ce92	07 	. 
	and e			;ce93	a3 	. 
	add a,b			;ce94	80 	. 
	ld b,b			;ce95	40 	@ 
	add a,c			;ce96	81 	. 
	rlca			;ce97	07 	. 
	and e			;ce98	a3 	. 
	add a,b			;ce99	80 	. 
	cp 080h		;ce9a	fe 80 	. . 
	ld a,(bc)			;ce9c	0a 	. 
	xor d			;ce9d	aa 	. 
	add a,b			;ce9e	80 	. 
	xor d			;ce9f	aa 	. 
	add a,b			;cea0	80 	. 
	rlca			;cea1	07 	. 
	and e			;cea2	a3 	. 
	add a,b			;cea3	80 	. 
	and b			;cea4	a0 	. 
	add a,b			;cea5	80 	. 
	rlca			;cea6	07 	. 
	and e			;cea7	a3 	. 
	add a,b			;cea8	80 	. 
	xor d			;cea9	aa 	. 
	add a,b			;ceaa	80 	. 
	ld a,(bc)			;ceab	0a 	. 
	xor d			;ceac	aa 	. 
	add a,b			;cead	80 	. 
	cp (hl)			;ceae	be 	. 
	add a,b			;ceaf	80 	. 
	ld a,(bc)			;ceb0	0a 	. 
	xor d			;ceb1	aa 	. 
	add a,b			;ceb2	80 	. 
	sub 080h		;ceb3	d6 80 	. . 
	ld a,(bc)			;ceb5	0a 	. 
	xor d			;ceb6	aa 	. 
	add a,b			;ceb7	80 	. 
	cp (hl)			;ceb8	be 	. 
	add a,b			;ceb9	80 	. 
	rlca			;ceba	07 	. 
	and e			;cebb	a3 	. 
	add a,b			;cebc	80 	. 
	jp po,00780h		;cebd	e2 80 07 	. . . 
	and e			;cec0	a3 	. 
	add a,b			;cec1	80 	. 
	cp 080h		;cec2	fe 80 	. . 
	rlca			;cec4	07 	. 
	and e			;cec5	a3 	. 
	add a,b			;cec6	80 	. 
	dec e			;cec7	1d 	. 
	add a,c			;cec8	81 	. 
	rlca			;cec9	07 	. 
	and e			;ceca	a3 	. 
	add a,b			;cecb	80 	. 
	ld b,b			;cecc	40 	@ 
	add a,c			;cecd	81 	. 
	rlca			;cece	07 	. 
	and e			;cecf	a3 	. 
	add a,b			;ced0	80 	. 
	ld d,e			;ced1	53 	S 
	add a,c			;ced2	81 	. 
	rlca			;ced3	07 	. 
	and e			;ced4	a3 	. 
	add a,b			;ced5	80 	. 
	cp 080h		;ced6	fe 80 	. . 
	ld a,(bc)			;ced8	0a 	. 
	xor d			;ced9	aa 	. 
	add a,b			;ceda	80 	. 
	sub 080h		;cedb	d6 80 	. . 
	rlca			;cedd	07 	. 
	and e			;cede	a3 	. 
	add a,b			;cedf	80 	. 
	xor d			;cee0	aa 	. 
	add a,b			;cee1	80 	. 
	ld a,(bc)			;cee2	0a 	. 
	xor d			;cee3	aa 	. 
	add a,b			;cee4	80 	. 
	sub 080h		;cee5	d6 80 	. . 
	ld a,(bc)			;cee7	0a 	. 
	xor d			;cee8	aa 	. 
	add a,b			;cee9	80 	. 
	jp po,00780h		;ceea	e2 80 07 	. . . 
	and e			;ceed	a3 	. 
	add a,b			;ceee	80 	. 
	sub 080h		;ceef	d6 80 	. . 
	ld a,(bc)			;cef1	0a 	. 
	xor d			;cef2	aa 	. 
	add a,b			;cef3	80 	. 
	cp (hl)			;cef4	be 	. 
	add a,b			;cef5	80 	. 
	rlca			;cef6	07 	. 
	and e			;cef7	a3 	. 
	add a,b			;cef8	80 	. 
	dec e			;cef9	1d 	. 
	add a,c			;cefa	81 	. 
	rlca			;cefb	07 	. 
	and e			;cefc	a3 	. 
	add a,b			;cefd	80 	. 
	cp 080h		;cefe	fe 80 	. . 
	rlca			;cf00	07 	. 
	and e			;cf01	a3 	. 
	add a,b			;cf02	80 	. 
	dec e			;cf03	1d 	. 
	add a,c			;cf04	81 	. 
	rlca			;cf05	07 	. 
	and e			;cf06	a3 	. 
	add a,b			;cf07	80 	. 
	ld b,b			;cf08	40 	@ 
	add a,c			;cf09	81 	. 
	ld a,(bc)			;cf0a	0a 	. 
	sbc a,b			;cf0b	98 	. 
	ld b,b			;cf0c	40 	@ 
	ld l,e			;cf0d	6b 	k 
	jr nc,$+9		;cf0e	30 07 	0 . 
	ld h,e			;cf10	63 	c 
	ld b,b			;cf11	40 	@ 
	adc a,a			;cf12	8f 	. 
	jr nc,$+9		;cf13	30 07 	0 . 
	ld h,e			;cf15	63 	c 
	ld b,b			;cf16	40 	@ 
	adc a,a			;cf17	8f 	. 
	jr nc,$+9		;cf18	30 07 	0 . 
	ld h,e			;cf1a	63 	c 
	ld b,b			;cf1b	40 	@ 
	adc a,a			;cf1c	8f 	. 
	jr nc,$+9		;cf1d	30 07 	0 . 
	ld h,e			;cf1f	63 	c 
	ld b,b			;cf20	40 	@ 
	ld l,e			;cf21	6b 	k 
	jr nc,$+9		;cf22	30 07 	0 . 
	ld h,e			;cf24	63 	c 
	ld b,b			;cf25	40 	@ 
	adc a,a			;cf26	8f 	. 
	jr nc,$+9		;cf27	30 07 	0 . 
	ld h,e			;cf29	63 	c 
	ld b,b			;cf2a	40 	@ 
	adc a,a			;cf2b	8f 	. 
	jr nc,$+9		;cf2c	30 07 	0 . 
	ld h,e			;cf2e	63 	c 
	ld b,b			;cf2f	40 	@ 
	adc a,a			;cf30	8f 	. 
	jr nc,$+9		;cf31	30 07 	0 . 
	ld h,e			;cf33	63 	c 
	ld b,b			;cf34	40 	@ 
	ld a,a			;cf35	7f 	 
	jr nc,$+9		;cf36	30 07 	0 . 
	ld h,e			;cf38	63 	c 
	ld b,b			;cf39	40 	@ 
	and b			;cf3a	a0 	. 
	jr nc,$+9		;cf3b	30 07 	0 . 
	ld h,e			;cf3d	63 	c 
	ld b,b			;cf3e	40 	@ 
	and b			;cf3f	a0 	. 
	jr nc,$+9		;cf40	30 07 	0 . 
	ld h,e			;cf42	63 	c 
	ld b,b			;cf43	40 	@ 
	and b			;cf44	a0 	. 
	jr nc,$+9		;cf45	30 07 	0 . 
	ld h,e			;cf47	63 	c 
	ld b,b			;cf48	40 	@ 
	ld a,a			;cf49	7f 	 
	jr nc,$+9		;cf4a	30 07 	0 . 
	ld h,e			;cf4c	63 	c 
	ld b,b			;cf4d	40 	@ 
	and b			;cf4e	a0 	. 
	jr nc,$+9		;cf4f	30 07 	0 . 
	ld h,e			;cf51	63 	c 
	ld b,b			;cf52	40 	@ 
	and b			;cf53	a0 	. 
	jr nc,$+9		;cf54	30 07 	0 . 
	ld h,e			;cf56	63 	c 
	ld b,b			;cf57	40 	@ 
	and b			;cf58	a0 	. 
	jr nc,$+9		;cf59	30 07 	0 . 
	ld h,e			;cf5b	63 	c 
	ld b,b			;cf5c	40 	@ 
	adc a,a			;cf5d	8f 	. 
	jr nc,$+9		;cf5e	30 07 	0 . 
	ld h,e			;cf60	63 	c 
	ld b,b			;cf61	40 	@ 
	ld (hl),c			;cf62	71 	q 
	jr nc,$+9		;cf63	30 07 	0 . 
	ld h,e			;cf65	63 	c 
	ld b,b			;cf66	40 	@ 
	ld (hl),c			;cf67	71 	q 
	jr nc,$+9		;cf68	30 07 	0 . 
	ld h,e			;cf6a	63 	c 
	ld b,b			;cf6b	40 	@ 
	ld (hl),c			;cf6c	71 	q 
	jr nc,$+9		;cf6d	30 07 	0 . 
	ld h,e			;cf6f	63 	c 
	ld b,b			;cf70	40 	@ 
	adc a,a			;cf71	8f 	. 
	jr nc,$+9		;cf72	30 07 	0 . 
	ld h,e			;cf74	63 	c 
	ld b,b			;cf75	40 	@ 
	ld (hl),c			;cf76	71 	q 
	jr nc,$+9		;cf77	30 07 	0 . 
	ld h,e			;cf79	63 	c 
	ld b,b			;cf7a	40 	@ 
	ld (hl),c			;cf7b	71 	q 
	jr nc,$+9		;cf7c	30 07 	0 . 
	ld h,e			;cf7e	63 	c 
	ld b,b			;cf7f	40 	@ 
	ld (hl),c			;cf80	71 	q 
	jr nc,$+9		;cf81	30 07 	0 . 
	ld h,e			;cf83	63 	c 
	ld b,b			;cf84	40 	@ 
	ld (hl),c			;cf85	71 	q 
	jr nc,$+9		;cf86	30 07 	0 . 
	ld h,e			;cf88	63 	c 
	ld b,b			;cf89	40 	@ 
	ld e,a			;cf8a	5f 	_ 
	jr nc,$+9		;cf8b	30 07 	0 . 
	ld h,e			;cf8d	63 	c 
	ld b,b			;cf8e	40 	@ 
	ld (hl),c			;cf8f	71 	q 
	jr nc,$+9		;cf90	30 07 	0 . 
	ld h,e			;cf92	63 	c 
	ld b,b			;cf93	40 	@ 
	ld e,a			;cf94	5f 	_ 
	jr nc,$+9		;cf95	30 07 	0 . 
	ld h,e			;cf97	63 	c 
	ld b,b			;cf98	40 	@ 
	ld e,a			;cf99	5f 	_ 
	jr nc,$+9		;cf9a	30 07 	0 . 
	ld h,e			;cf9c	63 	c 
	ld b,b			;cf9d	40 	@ 
	ld l,e			;cf9e	6b 	k 
	jr nc,$+9		;cf9f	30 07 	0 . 
	ld h,e			;cfa1	63 	c 
	ld b,b			;cfa2	40 	@ 
	ld l,e			;cfa3	6b 	k 
	jr nc,$+12		;cfa4	30 0a 	0 . 
	ld e,b			;cfa6	58 	X 
	add a,b			;cfa7	80 	. 
	adc a,a			;cfa8	8f 	. 
	ld d,b			;cfa9	50 	P 
	dec b			;cfaa	05 	. 
	add a,c			;cfab	81 	. 
	ld l,e			;cfac	6b 	k 
	add a,b			;cfad	80 	. 
	inc bc			;cfae	03 	. 
	ld d,l			;cfaf	55 	U 
	call po,0aa80h		;cfb0	e4 80 aa 	. . . 
	ld d,b			;cfb3	50 	P 
	dec b			;cfb4	05 	. 
	add a,c			;cfb5	81 	. 
	ld l,e			;cfb6	6b 	k 
	add a,b			;cfb7	80 	. 
	inc bc			;cfb8	03 	. 
	ld d,l			;cfb9	55 	U 
	call po,08f80h		;cfba	e4 80 8f 	. . . 
	ld d,b			;cfbd	50 	P 
	dec b			;cfbe	05 	. 
	add a,c			;cfbf	81 	. 
	ld l,e			;cfc0	6b 	k 
	add a,b			;cfc1	80 	. 
	inc bc			;cfc2	03 	. 
	ld d,l			;cfc3	55 	U 
	call po,05580h		;cfc4	e4 80 55 	. . U 
	ld d,b			;cfc7	50 	P 
	dec b			;cfc8	05 	. 
	add a,c			;cfc9	81 	. 
	ld l,e			;cfca	6b 	k 
	add a,b			;cfcb	80 	. 
	inc bc			;cfcc	03 	. 
	ld d,l			;cfcd	55 	U 
	call po,05f80h		;cfce	e4 80 5f 	. . _ 
	ld d,b			;cfd1	50 	P 
	dec b			;cfd2	05 	. 
	add a,c			;cfd3	81 	. 
	ld e,a			;cfd4	5f 	_ 
	add a,b			;cfd5	80 	. 
	inc bc			;cfd6	03 	. 
	ld d,l			;cfd7	55 	U 
	jp po,07f80h		;cfd8	e2 80 7f 	. .  
	ld d,b			;cfdb	50 	P 
	dec b			;cfdc	05 	. 
	add a,c			;cfdd	81 	. 
	ld e,a			;cfde	5f 	_ 
	add a,b			;cfdf	80 	. 
	inc bc			;cfe0	03 	. 
	ld d,l			;cfe1	55 	U 
	jp po,05080h		;cfe2	e2 80 50 	. . P 
	ld d,b			;cfe5	50 	P 
	dec b			;cfe6	05 	. 
	add a,c			;cfe7	81 	. 
	ld e,a			;cfe8	5f 	_ 
	add a,b			;cfe9	80 	. 
	inc bc			;cfea	03 	. 
	ld d,l			;cfeb	55 	U 
	jp po,06b80h		;cfec	e2 80 6b 	. . k 
	ld d,b			;cfef	50 	P 
	dec b			;cff0	05 	. 
	add a,c			;cff1	81 	. 
	ld e,a			;cff2	5f 	_ 
	add a,b			;cff3	80 	. 
	inc bc			;cff4	03 	. 
	ld d,l			;cff5	55 	U 
	jp po,07180h		;cff6	e2 80 71 	. . q 
	ld d,b			;cff9	50 	P 
	dec b			;cffa	05 	. 
	add a,c			;cffb	81 	. 
	ld (hl),c			;cffc	71 	q 
	add a,b			;cffd	80 	. 
	inc bc			;cffe	03 	. 
	ld d,l			;cfff	55 	U 
	sub 080h		;d000	d6 80 	. . 
	ld b,a			;d002	47 	G 
	ld d,b			;d003	50 	P 
	dec b			;d004	05 	. 
	add a,c			;d005	81 	. 
	ld (hl),c			;d006	71 	q 
	add a,b			;d007	80 	. 
	inc bc			;d008	03 	. 
	ld d,l			;d009	55 	U 
	sub 080h		;d00a	d6 80 	. . 
	ld a,a			;d00c	7f 	 
	ld d,b			;d00d	50 	P 
	dec b			;d00e	05 	. 
	add a,c			;d00f	81 	. 
	ld (hl),c			;d010	71 	q 
	add a,b			;d011	80 	. 
	inc bc			;d012	03 	. 
	ld d,l			;d013	55 	U 
	sub 080h		;d014	d6 80 	. . 
	ld d,b			;d016	50 	P 
	ld d,b			;d017	50 	P 
	dec b			;d018	05 	. 
	add a,c			;d019	81 	. 
	ld (hl),c			;d01a	71 	q 
	add a,b			;d01b	80 	. 
	inc bc			;d01c	03 	. 
	ld d,l			;d01d	55 	U 
	sub 080h		;d01e	d6 80 	. . 
	ld d,l			;d020	55 	U 
	ld d,b			;d021	50 	P 
	dec b			;d022	05 	. 
	add a,c			;d023	81 	. 
	ld (hl),c			;d024	71 	q 
	add a,b			;d025	80 	. 
	inc bc			;d026	03 	. 
	ld d,l			;d027	55 	U 
	sub 080h		;d028	d6 80 	. . 
	ld e,a			;d02a	5f 	_ 
	ld d,b			;d02b	50 	P 
	dec b			;d02c	05 	. 
	add a,c			;d02d	81 	. 
	ld (hl),c			;d02e	71 	q 
	add a,b			;d02f	80 	. 
	inc bc			;d030	03 	. 
	ld d,l			;d031	55 	U 
	sub 080h		;d032	d6 80 	. . 
	ld l,e			;d034	6b 	k 
	ld d,b			;d035	50 	P 
	dec b			;d036	05 	. 
	add a,c			;d037	81 	. 
	ld b,a			;d038	47 	G 
	add a,b			;d039	80 	. 
	inc bc			;d03a	03 	. 
	ld d,l			;d03b	55 	U 
	ld b,a			;d03c	47 	G 
	add a,b			;d03d	80 	. 
	sub 050h		;d03e	d6 50 	. P 
	ld a,(bc)			;d040	0a 	. 
	sbc a,b			;d041	98 	. 
	ld b,b			;d042	40 	@ 
	and b			;d043	a0 	. 
	jr nc,$+24		;d044	30 16 	0 . 
	ld b,b			;d046	40 	@ 
	ld l,e			;d047	6b 	k 
	jr nc,$+9		;d048	30 07 	0 . 
	ld h,h			;d04a	64 	d 
	ld b,b			;d04b	40 	@ 
	ld l,e			;d04c	6b 	k 
	jr nc,$+9		;d04d	30 07 	0 . 
	ld h,h			;d04f	64 	d 
	ld b,b			;d050	40 	@ 
	ld a,a			;d051	7f 	 
	jr nc,$+13		;d052	30 0b 	0 . 
	ld l,e			;d054	6b 	k 
	ld b,b			;d055	40 	@ 
	and b			;d056	a0 	. 
	jr nc,$+13		;d057	30 0b 	0 . 
	ld l,e			;d059	6b 	k 
	ld b,b			;d05a	40 	@ 
	and b			;d05b	a0 	. 
	jr nc,$+24		;d05c	30 16 	0 . 
	ld b,b			;d05e	40 	@ 
	ld l,e			;d05f	6b 	k 
	jr nc,$+9		;d060	30 07 	0 . 
	ld h,h			;d062	64 	d 
	ld b,b			;d063	40 	@ 
	ld l,e			;d064	6b 	k 
	jr nc,$+9		;d065	30 07 	0 . 
	ld h,h			;d067	64 	d 
	ld b,b			;d068	40 	@ 
	ld a,a			;d069	7f 	 
	jr nc,$+13		;d06a	30 0b 	0 . 
	ld l,e			;d06c	6b 	k 
	ld b,b			;d06d	40 	@ 
	and b			;d06e	a0 	. 
	jr nc,$+13		;d06f	30 0b 	0 . 
	ld l,e			;d071	6b 	k 
	ld b,b			;d072	40 	@ 
	adc a,a			;d073	8f 	. 
	jr nc,$+13		;d074	30 0b 	0 . 
	ld l,e			;d076	6b 	k 
	ld b,b			;d077	40 	@ 
	ld l,e			;d078	6b 	k 
	jr nc,$+9		;d079	30 07 	0 . 
	ld h,h			;d07b	64 	d 
	ld b,b			;d07c	40 	@ 
	ld l,e			;d07d	6b 	k 
	jr nc,$+9		;d07e	30 07 	0 . 
	ld h,h			;d080	64 	d 
	ld b,b			;d081	40 	@ 
	ld l,e			;d082	6b 	k 
	jr nc,$+24		;d083	30 16 	0 . 
	halt			;d085	76 	v 
	halt			;d086	76 	v 
	ld b,b			;d087	40 	@ 
	ld d,l			;d088	55 	U 
	jr nc,$+13		;d089	30 0b 	0 . 
	ld l,e			;d08b	6b 	k 
	ld b,b			;d08c	40 	@ 
	ld d,b			;d08d	50 	P 
	jr nc,$+13		;d08e	30 0b 	0 . 
	ld d,b			;d090	50 	P 
	or (hl)			;d091	b6 	. 
	or (hl)			;d092	b6 	. 
	add a,b			;d093	80 	. 
	ld b,b			;d094	40 	@ 
	ld d,c			;d095	51 	Q 
	ld d,080h		;d096	16 80 	. . 
	sub 050h		;d098	d6 50 	. P 
	rlca			;d09a	07 	. 
	and h			;d09b	a4 	. 
	add a,b			;d09c	80 	. 
	sub 050h		;d09d	d6 50 	. P 
	rlca			;d09f	07 	. 
	and h			;d0a0	a4 	. 
	add a,b			;d0a1	80 	. 
	cp 050h		;d0a2	fe 50 	. P 
	dec bc			;d0a4	0b 	. 
	xor e			;d0a5	ab 	. 
	add a,b			;d0a6	80 	. 
	ld b,b			;d0a7	40 	@ 
	ld d,c			;d0a8	51 	Q 
	dec bc			;d0a9	0b 	. 
	xor e			;d0aa	ab 	. 
	add a,b			;d0ab	80 	. 
	ld b,b			;d0ac	40 	@ 
	ld d,c			;d0ad	51 	Q 
	ld d,080h		;d0ae	16 80 	. . 
	sub 050h		;d0b0	d6 50 	. P 
	rlca			;d0b2	07 	. 
	and h			;d0b3	a4 	. 
	add a,b			;d0b4	80 	. 
	sub 050h		;d0b5	d6 50 	. P 
	rlca			;d0b7	07 	. 
	and h			;d0b8	a4 	. 
	add a,b			;d0b9	80 	. 
	ret p			;d0ba	f0 	. 
	ld h,b			;d0bb	60 	` 
	dec bc			;d0bc	0b 	. 
	xor e			;d0bd	ab 	. 
	add a,b			;d0be	80 	. 
	cp 060h		;d0bf	fe 60 	. ` 
	dec bc			;d0c1	0b 	. 
	xor e			;d0c2	ab 	. 
	add a,b			;d0c3	80 	. 
	dec e			;d0c4	1d 	. 
	ld h,c			;d0c5	61 	a 
	dec bc			;d0c6	0b 	. 
	xor e			;d0c7	ab 	. 
	add a,b			;d0c8	80 	. 
	ld d,a			;d0c9	57 	W 
	ld h,e			;d0ca	63 	c 
	rlca			;d0cb	07 	. 
	and h			;d0cc	a4 	. 
	add a,b			;d0cd	80 	. 
	ld d,a			;d0ce	57 	W 
	ld h,e			;d0cf	63 	c 
	rlca			;d0d0	07 	. 
	and h			;d0d1	a4 	. 
	add a,b			;d0d2	80 	. 
	ld d,a			;d0d3	57 	W 
	ld h,e			;d0d4	63 	c 
	ld d,080h		;d0d5	16 80 	. . 
	sub 070h		;d0d7	d6 70 	. p 
	dec bc			;d0d9	0b 	. 
	ld l,e			;d0da	6b 	k 
	add a,b			;d0db	80 	. 
	ld b,b			;d0dc	40 	@ 
	ld (hl),c			;d0dd	71 	q 
	dec bc			;d0de	0b 	. 
	sub b			;d0df	90 	. 
	ld b,c			;d0e0	41 	A 
	xor d			;d0e1	aa 	. 
	jr nc,$+4		;d0e2	30 02 	0 . 
	xor d			;d0e4	aa 	. 
	inc d			;d0e5	14 	. 
	ld b,c			;d0e6	41 	A 
	sub 030h		;d0e7	d6 30 	. 0 
	ld (bc),a			;d0e9	02 	. 
	xor d			;d0ea	aa 	. 
	ret pe			;d0eb	e8 	. 
	ld b,d			;d0ec	42 	B 
	xor d			;d0ed	aa 	. 
	jr nc,$+12		;d0ee	30 0a 	0 . 
	inc (hl)			;d0f0	34 	4 
	dec d			;d0f1	15 	. 
	ld b,c			;d0f2	41 	A 
	cp (hl)			;d0f3	be 	. 
	jr nc,$+4		;d0f4	30 02 	0 . 
	push af			;d0f6	f5 	. 
	jr $+68		;d0f7	18 42 	. B 
	cp 030h		;d0f9	fe 30 	. 0 
	ld a,(bc)			;d0fb	0a 	. 
	inc (hl)			;d0fc	34 	4 
	dec d			;d0fd	15 	. 
	ld b,c			;d0fe	41 	A 
	jp z,00230h		;d0ff	ca 30 02 	. 0 . 
	xor d			;d102	aa 	. 
	jr $+67		;d103	18 41 	. A 
	cp 030h		;d105	fe 30 	. 0 
	ld (bc),a			;d107	02 	. 
	xor d			;d108	aa 	. 
	call po,0ca42h		;d109	e4 42 ca 	. B . 
	jr nc,$+12		;d10c	30 0a 	0 . 
	inc (hl)			;d10e	34 	4 
	dec d			;d10f	15 	. 
	ld b,c			;d110	41 	A 
	jp po,00230h		;d111	e2 30 02 	. 0 . 
	push af			;d114	f5 	. 
	inc e			;d115	1c 	. 
	ld b,c			;d116	41 	A 
	sub 030h		;d117	d6 30 	. 0 
	ld (bc),a			;d119	02 	. 
	xor d			;d11a	aa 	. 
	inc c			;d11b	0c 	. 
	ld b,c			;d11c	41 	A 
	ret p			;d11d	f0 	. 
	jr nc,$+4		;d11e	30 02 	0 . 
	and l			;d120	a5 	. 
	jp p,0fe41h		;d121	f2 41 fe 	. A . 
	jr nc,$+4		;d124	30 02 	0 . 
	and l			;d126	a5 	. 
	rra			;d127	1f 	. 
	ld b,d			;d128	42 	B 
	jp z,00a30h		;d129	ca 30 0a 	. 0 . 
	inc (hl)			;d12c	34 	4 
	dec d			;d12d	15 	. 
	ld b,c			;d12e	41 	A 
	sub 030h		;d12f	d6 30 	. 0 
	ld (bc),a			;d131	02 	. 
	and l			;d132	a5 	. 
	call p,0e241h		;d133	f4 41 e2 	. A . 
	jr nc,$+4		;d136	30 02 	0 . 
	and l			;d138	a5 	. 
	inc e			;d139	1c 	. 
	ld b,d			;d13a	42 	B 
	cp (hl)			;d13b	be 	. 
	jr nc,$+12		;d13c	30 0a 	0 . 
	inc (hl)			;d13e	34 	4 
	dec d			;d13f	15 	. 
	ld b,c			;d140	41 	A 
	cp 030h		;d141	fe 30 	. 0 
	ld (bc),a			;d143	02 	. 
	and l			;d144	a5 	. 
	call po,0fe41h		;d145	e4 41 fe 	. A . 
	jr nc,$+4		;d148	30 02 	0 . 
	and l			;d14a	a5 	. 
	jr nc,$+68		;d14b	30 42 	0 B 
	ld a,l			;d14d	7d 	} 
	ld sp,03414h		;d14e	31 14 34 	1 . 4 
	dec d			;d151	15 	. 
	ld b,d			;d152	42 	B 
	cp (hl)			;d153	be 	. 
	jr nc,$+22		;d154	30 14 	0 . 
	inc (hl)			;d156	34 	4 
	dec d			;d157	15 	. 
	ld d,b			;d158	50 	P 
	add a,d			;d159	82 	. 
	xor h			;d15a	ac 	. 
	ld sp,03414h		;d15b	31 14 34 	1 . 4 
	dec d			;d15e	15 	. 
	add a,d			;d15f	82 	. 
	dec e			;d160	1d 	. 
	ld sp,03414h		;d161	31 14 34 	1 . 4 
	dec d			;d164	15 	. 
	add a,d			;d165	82 	. 
	xor h			;d166	ac 	. 
	ld sp,03414h		;d167	31 14 34 	1 . 4 
	dec d			;d16a	15 	. 
	add a,c			;d16b	81 	. 
	call m,00231h		;d16c	fc 31 02 	. 1 . 
	xor d			;d16f	aa 	. 
	call po,0c582h		;d170	e4 82 c5 	. . . 
	ld sp,03414h		;d173	31 14 34 	1 . 4 
	dec d			;d176	15 	. 
	add a,d			;d177	82 	. 
	ld l,031h		;d178	2e 31 	. 1 
	inc d			;d17a	14 	. 
	inc (hl)			;d17b	34 	4 
	dec d			;d17c	15 	. 
	add a,d			;d17d	82 	. 
	push bc			;d17e	c5 	. 
	ld sp,03414h		;d17f	31 14 34 	1 . 4 
	dec d			;d182	15 	. 
	add a,c			;d183	81 	. 
	ld l,031h		;d184	2e 31 	. 1 
	ld (bc),a			;d186	02 	. 
	xor d			;d187	aa 	. 
	ld (de),a			;d188	12 	. 
	add a,d			;d189	82 	. 
	ld d,e			;d18a	53 	S 
	ld sp,03414h		;d18b	31 14 34 	1 . 4 
	dec d			;d18e	15 	. 
	add a,d			;d18f	82 	. 
	push bc			;d190	c5 	. 
	ld sp,03414h		;d191	31 14 34 	1 . 4 
	dec d			;d194	15 	. 
	add a,d			;d195	82 	. 
	call m,01431h		;d196	fc 31 14 	. 1 . 
	inc (hl)			;d199	34 	4 
	dec d			;d19a	15 	. 
	add a,d			;d19b	82 	. 
	sub h			;d19c	94 	. 
	ld sp,03414h		;d19d	31 14 34 	1 . 4 
	dec d			;d1a0	15 	. 
	add a,d			;d1a1	82 	. 
	ld a,l			;d1a2	7d 	} 
	ld sp,03414h		;d1a3	31 14 34 	1 . 4 
	dec d			;d1a6	15 	. 
	add a,d			;d1a7	82 	. 
	call m,01431h		;d1a8	fc 31 14 	. 1 . 
	inc (hl)			;d1ab	34 	4 
	dec d			;d1ac	15 	. 
	add a,c			;d1ad	81 	. 
	ld a,l			;d1ae	7d 	} 
	ld sp,0aa02h		;d1af	31 02 aa 	1 . . 
	ld a,a			;d1b2	7f 	 
	add a,d			;d1b3	82 	. 
	ld a,l			;d1b4	7d 	} 
	ld sp,03414h		;d1b5	31 14 34 	1 . 4 
	dec d			;d1b8	15 	. 
	sub b			;d1b9	90 	. 
	ld l,c			;d1ba	69 	i 
	ld b,b			;d1bb	40 	@ 
	or h			;d1bc	b4 	. 
	jr nc,$+8		;d1bd	30 06 	0 . 
	ld h,e			;d1bf	63 	c 
	ld b,b			;d1c0	40 	@ 
	adc a,a			;d1c1	8f 	. 
	jr nc,$+8		;d1c2	30 06 	0 . 
	ld h,e			;d1c4	63 	c 
	ld b,b			;d1c5	40 	@ 
	add a,a			;d1c6	87 	. 
	jr nc,$+8		;d1c7	30 06 	0 . 
	ld h,e			;d1c9	63 	c 
	ld b,b			;d1ca	40 	@ 
	ld a,b			;d1cb	78 	x 
	jr nc,$+11		;d1cc	30 09 	0 . 
	ld l,c			;d1ce	69 	i 
	ld b,b			;d1cf	40 	@ 
	ld e,d			;d1d0	5a 	Z 
	jr nc,$+11		;d1d1	30 09 	0 . 
	ld l,c			;d1d3	69 	i 
	ld b,b			;d1d4	40 	@ 
	ld e,a			;d1d5	5f 	_ 
	jr nc,$+11		;d1d6	30 09 	0 . 
	ld l,c			;d1d8	69 	i 
	ld b,b			;d1d9	40 	@ 
	ld l,e			;d1da	6b 	k 
	jr nc,$+11		;d1db	30 09 	0 . 
	ld l,c			;d1dd	69 	i 
	ld b,b			;d1de	40 	@ 
	adc a,a			;d1df	8f 	. 
	jr nc,$+29		;d1e0	30 1b 	0 . 
	ld (hl),d			;d1e2	72 	r 
	ld b,b			;d1e3	40 	@ 
	adc a,a			;d1e4	8f 	. 
	jr nc,$+8		;d1e5	30 06 	0 . 
	ld h,e			;d1e7	63 	c 
	ld b,b			;d1e8	40 	@ 
	add a,a			;d1e9	87 	. 
	jr nc,$+8		;d1ea	30 06 	0 . 
	ld h,e			;d1ec	63 	c 
	ld b,b			;d1ed	40 	@ 
	adc a,a			;d1ee	8f 	. 
	jr nc,$+8		;d1ef	30 06 	0 . 
	ld h,e			;d1f1	63 	c 
	ld b,b			;d1f2	40 	@ 
	and b			;d1f3	a0 	. 
	jr nc,$+29		;d1f4	30 1b 	0 . 
	ld (hl),d			;d1f6	72 	r 
	ld b,b			;d1f7	40 	@ 
	and b			;d1f8	a0 	. 
	jr nc,$+8		;d1f9	30 06 	0 . 
	ld h,e			;d1fb	63 	c 
	ld b,b			;d1fc	40 	@ 
	adc a,a			;d1fd	8f 	. 
	jr nc,$+8		;d1fe	30 06 	0 . 
	ld h,e			;d200	63 	c 
	ld b,b			;d201	40 	@ 
	and b			;d202	a0 	. 
	jr nc,$+8		;d203	30 06 	0 . 
	ld h,e			;d205	63 	c 
	ld b,b			;d206	40 	@ 
	or h			;d207	b4 	. 
	jr nc,$+29		;d208	30 1b 	0 . 
	ld l,c			;d20a	69 	i 
	ld e,b			;d20b	58 	X 
	add a,b			;d20c	80 	. 
	jp z,00652h		;d20d	ca 52 06 	. R . 
	and e			;d210	a3 	. 
	add a,b			;d211	80 	. 
	dec e			;d212	1d 	. 
	ld b,c			;d213	41 	A 
	ld b,0a3h		;d214	06 a3 	. . 
	add a,b			;d216	80 	. 
	dec e			;d217	1d 	. 
	ld d,c			;d218	51 	Q 
	ld b,0a3h		;d219	06 a3 	. . 
	add a,b			;d21b	80 	. 
	dec e			;d21c	1d 	. 
	ld h,c			;d21d	61 	a 
	ld b,0a3h		;d21e	06 a3 	. . 
	add a,b			;d220	80 	. 
	jp m,00642h		;d221	fa 42 06 	. B . 
	and e			;d224	a3 	. 
	add a,b			;d225	80 	. 
	dec e			;d226	1d 	. 
	ld b,c			;d227	41 	A 
	ld b,0a3h		;d228	06 a3 	. . 
	add a,b			;d22a	80 	. 
	dec e			;d22b	1d 	. 
	ld d,c			;d22c	51 	Q 
	ld b,0a3h		;d22d	06 a3 	. . 
	add a,b			;d22f	80 	. 
	dec e			;d230	1d 	. 
	ld h,c			;d231	61 	a 
	ld b,0a3h		;d232	06 a3 	. . 
	add a,b			;d234	80 	. 
	ld d,a			;d235	57 	W 
	inc sp			;d236	33 	3 
	ld b,0a3h		;d237	06 a3 	. . 
	add a,b			;d239	80 	. 
	dec e			;d23a	1d 	. 
	ld b,c			;d23b	41 	A 
	ld b,0a3h		;d23c	06 a3 	. . 
	add a,b			;d23e	80 	. 
	dec e			;d23f	1d 	. 
	ld d,c			;d240	51 	Q 
	ld b,0a3h		;d241	06 a3 	. . 
	add a,b			;d243	80 	. 
	dec e			;d244	1d 	. 
	ld h,c			;d245	61 	a 
	ld b,0a3h		;d246	06 a3 	. . 
	add a,b			;d248	80 	. 
	cp a			;d249	bf 	. 
	inc sp			;d24a	33 	3 
	ld b,0a3h		;d24b	06 a3 	. . 
	add a,b			;d24d	80 	. 
	dec e			;d24e	1d 	. 
	ld b,c			;d24f	41 	A 
	ld b,0a3h		;d250	06 a3 	. . 
	add a,b			;d252	80 	. 
	dec e			;d253	1d 	. 
	ld d,c			;d254	51 	Q 
	ld b,0a3h		;d255	06 a3 	. . 
	add a,b			;d257	80 	. 
	dec e			;d258	1d 	. 
	ld h,c			;d259	61 	a 
	ld b,0a3h		;d25a	06 a3 	. . 
	add a,b			;d25c	80 	. 
	jp z,00652h		;d25d	ca 52 06 	. R . 
	and e			;d260	a3 	. 
	add a,b			;d261	80 	. 
	dec e			;d262	1d 	. 
	ld b,c			;d263	41 	A 
	ld b,0a3h		;d264	06 a3 	. . 
	add a,b			;d266	80 	. 
	dec e			;d267	1d 	. 
	ld d,c			;d268	51 	Q 
	ld b,0a3h		;d269	06 a3 	. . 
	add a,b			;d26b	80 	. 
	dec e			;d26c	1d 	. 
	ld h,c			;d26d	61 	a 
	ld b,0a3h		;d26e	06 a3 	. . 
	add a,b			;d270	80 	. 
	ret po			;d271	e0 	. 
	ld d,c			;d272	51 	Q 
	ld b,0a3h		;d273	06 a3 	. . 
	add a,b			;d275	80 	. 
	dec c			;d276	0d 	. 
	ld b,c			;d277	41 	A 
	ld b,0a3h		;d278	06 a3 	. . 
	add a,b			;d27a	80 	. 
	dec c			;d27b	0d 	. 
	ld d,c			;d27c	51 	Q 
	ld b,0a3h		;d27d	06 a3 	. . 
	add a,b			;d27f	80 	. 
	dec c			;d280	0d 	. 
	ld h,c			;d281	61 	a 
	ld b,0a3h		;d282	06 a3 	. . 
	add a,b			;d284	80 	. 
	jp m,00642h		;d285	fa 42 06 	. B . 
	and e			;d288	a3 	. 
	add a,b			;d289	80 	. 
	dec c			;d28a	0d 	. 
	ld b,c			;d28b	41 	A 
	ld b,0a3h		;d28c	06 a3 	. . 
	add a,b			;d28e	80 	. 
	dec c			;d28f	0d 	. 
	ld d,c			;d290	51 	Q 
	ld b,0a3h		;d291	06 a3 	. . 
	add a,b			;d293	80 	. 
	dec c			;d294	0d 	. 
	ld h,c			;d295	61 	a 
	ld b,0a3h		;d296	06 a3 	. . 
	add a,b			;d298	80 	. 
	jp z,00652h		;d299	ca 52 06 	. R . 
	and e			;d29c	a3 	. 
	add a,b			;d29d	80 	. 
	cp a			;d29e	bf 	. 
	inc hl			;d29f	23 	# 
	ld b,0a3h		;d2a0	06 a3 	. . 
	add a,b			;d2a2	80 	. 
	ld d,a			;d2a3	57 	W 
	inc sp			;d2a4	33 	3 
	ld b,0a3h		;d2a5	06 a3 	. . 
	add a,b			;d2a7	80 	. 
	jp m,00642h		;d2a8	fa 42 06 	. B . 
	and e			;d2ab	a3 	. 
	sbc a,b			;d2ac	98 	. 
	ld b,c			;d2ad	41 	A 
	rst 38h			;d2ae	ff 	. 
	ld (hl),e			;d2af	73 	s 
	inc b			;d2b0	04 	. 
	inc d			;d2b1	14 	. 
	ld de,05868h		;d2b2	11 68 58 	. h X 
	ld (bc),a			;d2b5	02 	. 
	ld (de),a			;d2b6	12 	. 
	inc b			;d2b7	04 	. 
	inc d			;d2b8	14 	. 
	ld de,05002h		;d2b9	11 02 50 	. . P 
	inc c			;d2bc	0c 	. 
	ld d,e			;d2bd	53 	S 
	inc de			;d2be	13 	. 
	jr $+1		;d2bf	18 ff 	. . 
	rst 38h			;d2c1	ff 	. 
	rst 38h			;d2c2	ff 	. 
	rst 38h			;d2c3	ff 	. 
	rst 38h			;d2c4	ff 	. 
	rst 38h			;d2c5	ff 	. 
	rst 38h			;d2c6	ff 	. 
	rst 38h			;d2c7	ff 	. 
	rst 38h			;d2c8	ff 	. 
	rst 38h			;d2c9	ff 	. 
	rst 38h			;d2ca	ff 	. 
	rst 38h			;d2cb	ff 	. 
	rst 38h			;d2cc	ff 	. 
	rst 38h			;d2cd	ff 	. 
	rst 38h			;d2ce	ff 	. 
	rst 38h			;d2cf	ff 	. 
	rst 38h			;d2d0	ff 	. 
	rst 38h			;d2d1	ff 	. 
	rst 38h			;d2d2	ff 	. 
	rst 38h			;d2d3	ff 	. 
	rst 38h			;d2d4	ff 	. 
	rst 38h			;d2d5	ff 	. 
	rst 38h			;d2d6	ff 	. 
	rst 38h			;d2d7	ff 	. 
	rst 38h			;d2d8	ff 	. 
	rst 38h			;d2d9	ff 	. 
	rst 38h			;d2da	ff 	. 
	rst 38h			;d2db	ff 	. 
	rst 38h			;d2dc	ff 	. 
	rst 38h			;d2dd	ff 	. 
	rst 38h			;d2de	ff 	. 
	rst 38h			;d2df	ff 	. 
	rst 38h			;d2e0	ff 	. 
	rst 38h			;d2e1	ff 	. 
	rst 38h			;d2e2	ff 	. 
	rst 38h			;d2e3	ff 	. 
	rst 38h			;d2e4	ff 	. 
	rst 38h			;d2e5	ff 	. 
	rst 38h			;d2e6	ff 	. 
	rst 38h			;d2e7	ff 	. 
	rst 38h			;d2e8	ff 	. 
	rst 38h			;d2e9	ff 	. 
	rst 38h			;d2ea	ff 	. 
	rst 38h			;d2eb	ff 	. 
	rst 38h			;d2ec	ff 	. 
	rst 38h			;d2ed	ff 	. 
	rst 38h			;d2ee	ff 	. 
	rst 38h			;d2ef	ff 	. 
	rst 38h			;d2f0	ff 	. 
	rst 38h			;d2f1	ff 	. 
	rst 38h			;d2f2	ff 	. 
	rst 38h			;d2f3	ff 	. 
	rst 38h			;d2f4	ff 	. 
	rst 38h			;d2f5	ff 	. 
	rst 38h			;d2f6	ff 	. 
	rst 38h			;d2f7	ff 	. 
	rst 38h			;d2f8	ff 	. 
	rst 38h			;d2f9	ff 	. 
	rst 38h			;d2fa	ff 	. 
	rst 38h			;d2fb	ff 	. 
	rst 38h			;d2fc	ff 	. 
	rst 38h			;d2fd	ff 	. 
	rst 38h			;d2fe	ff 	. 
	rst 38h			;d2ff	ff 	. 
	set 0,(hl)		;d300	cb c6 	. . 
	ld hl,005a0h		;d302	21 a0 05 	! . . 
	xor a			;d305	af 	. 
	jp 0b895h		;d306	c3 95 b8 	. . . 
	ld hl,07272h		;d309	21 72 72 	! r r 
	bit 5,(hl)		;d30c	cb 6e 	. n 
	jr z,$+11		;d30e	28 09 	( . 
	res 5,(hl)		;d310	cb ae 	. . 
	push iy		;d312	fd e5 	. . 
	call 0c9d2h		;d314	cd d2 c9 	. . . 
	pop iy		;d317	fd e1 	. . 
	jp 0a596h		;d319	c3 96 a5 	. . . 
	ld a,(07272h)		;d31c	3a 72 72 	: r r 
	bit 5,a		;d31f	cb 6f 	. o 
	ret nz			;d321	c0 	. 
	call 0c9e9h		;d322	cd e9 c9 	. . . 
	ret			;d325	c9 	. 
	call 0b8f7h		;d326	cd f7 b8 	. . . 
	push iy		;d329	fd e5 	. . 
	call 0ca24h		;d32b	cd 24 ca 	. $ . 
	ld hl,0726eh		;d32e	21 6e 72 	! n r 
	set 7,(hl)		;d331	cb fe 	. . 
	bit 7,(hl)		;d333	cb 7e 	. ~ 
	jr nz,$-2		;d335	20 fc 	  . 
	ld bc,001e2h		;d337	01 e2 01 	. . . 
	call 01fd9h		;d33a	cd d9 1f 	. . . 
	call 0ca36h		;d33d	cd 36 ca 	. 6 . 
	pop iy		;d340	fd e1 	. . 
	jp 0b8abh		;d342	c3 ab b8 	. . . 
	call 0ca2dh		;d345	cd 2d ca 	. - . 
	ld hl,0726eh		;d348	21 6e 72 	! n r 
	set 7,(hl)		;d34b	cb fe 	. . 
	bit 7,(hl)		;d34d	cb 7e 	. ~ 
	jr nz,$-2		;d34f	20 fc 	  . 
	ld bc,001e2h		;d351	01 e2 01 	. . . 
	call 01fd9h		;d354	cd d9 1f 	. . . 
	ld hl,07272h		;d357	21 72 72 	! r r 
	jp 0b875h		;d35a	c3 75 b8 	. u . 
	ld (0726fh),a		;d35d	32 6f 72 	2 o r 
	call 0c9e9h		;d360	cd e9 c9 	. . . 
	jp 0b89bh		;d363	c3 9b b8 	. . . 
	call 09577h		;d366	cd 77 95 	. w . 
	xor a			;d369	af 	. 
	jp 09481h		;d36a	c3 81 94 	. . . 
	ld (072c6h),a		;d36d	32 c6 72 	2 . r 
	ld hl,072c4h		;d370	21 c4 72 	! . r 
	bit 0,(hl)		;d373	cb 46 	. F 
	jp z,0b8ech		;d375	ca ec b8 	. . . 
	res 0,(hl)		;d378	cb 86 	. . 
	ld a,(0726fh)		;d37a	3a 6f 72 	: o r 
	call 01fd0h		;d37d	cd d0 1f 	. . . 
	jp 0b8ech		;d380	c3 ec b8 	. . . 
	ld a,(072c6h)		;d383	3a c6 72 	: . r 
	call 01fd0h		;d386	cd d0 1f 	. . . 
	and a			;d389	a7 	. 
	jp z,0d3a6h		;d38a	ca a6 d3 	. . . 
	ld a,(072c3h)		;d38d	3a c3 72 	: . r 
	xor 001h		;d390	ee 01 	. . 
	ld (072c3h),a		;d392	32 c3 72 	2 . r 
	ld hl,00078h		;d395	21 78 00 	! x . 
	bit 0,a		;d398	cb 47 	. G 
	jr z,$+5		;d39a	28 03 	( . 
	ld hl,0003ch		;d39c	21 3c 00 	! < . 
	xor a			;d39f	af 	. 
	call 01fcdh		;d3a0	cd cd 1f 	. . . 
	ld (072c6h),a		;d3a3	32 c6 72 	2 . r 
	ld a,(072c3h)		;d3a6	3a c3 72 	: . r 
	bit 0,a		;d3a9	cb 47 	. G 
	jp z,0a853h		;d3ab	ca 53 a8 	. S . 
	jp 0a858h		;d3ae	c3 58 a8 	. X . 
	jr z,$+15		;d3b1	28 0d 	( . 
	ld a,(ix+001h)		;d3b3	dd 7e 01 	. ~ . 
	and 00dh		;d3b6	e6 0d 	. . 
	ld a,001h		;d3b8	3e 01 	> . 
	jp z,09558h		;d3ba	ca 58 95 	. X . 
	jp 09555h		;d3bd	c3 55 95 	. U . 
	inc a			;d3c0	3c 	< 
	bit 3,(ix+001h)		;d3c1	dd cb 01 5e 	. . . ^ 
	jp z,09547h		;d3c5	ca 47 95 	. G . 
	ld a,(ix+001h)		;d3c8	dd 7e 01 	. ~ . 
	and 007h		;d3cb	e6 07 	. . 
	ld a,002h		;d3cd	3e 02 	> . 
	jp z,09558h		;d3cf	ca 58 95 	. X . 
	jp 09555h		;d3d2	c3 55 95 	. U . 
	and 007h		;d3d5	e6 07 	. . 
	ld c,0c0h		;d3d7	0e c0 	. . 
	cp 003h		;d3d9	fe 03 	. . 
	jp 0a8afh		;d3db	c3 af a8 	. . . 
	call 01ff1h		;d3de	cd f1 1f 	. . . 
	ld a,0ffh		;d3e1	3e ff 	> . 
	ld (0702bh),a		;d3e3	32 2b 70 	2 + p 
	ld (07035h),a		;d3e6	32 35 70 	2 5 p 
	ret			;d3e9	c9 	. 
	call 01ff1h		;d3ea	cd f1 1f 	. . . 
	ld a,0ffh		;d3ed	3e ff 	> . 
	ld (0702bh),a		;d3ef	32 2b 70 	2 + p 
	ld (07035h),a		;d3f2	32 35 70 	2 5 p 
	ld (07067h),a		;d3f5	32 67 70 	2 g p 
	ret			;d3f8	c9 	. 
	ld a,(0702bh)		;d3f9	3a 2b 70 	: + p 
	and 00fh		;d3fc	e6 0f 	. . 
	cp 002h		;d3fe	fe 02 	. . 
	jr z,$+5		;d400	28 03 	( . 
	call 0c960h		;d402	cd 60 c9 	. ` . 
	call 0999fh		;d405	cd 9f 99 	. . . 
	jp 098a5h		;d408	c3 a5 98 	. . . 
	ld a,(07273h)		;d40b	3a 73 72 	: s r 
	bit 7,a		;d40e	cb 7f 	.  
	jp z,0d3f9h		;d410	ca f9 d3 	. . . 
	ld a,(0707bh)		;d413	3a 7b 70 	: { p 
	and 0ffh		;d416	e6 ff 	. . 
	cp 0ffh		;d418	fe ff 	. . 
	jp nz,0d405h		;d41a	c2 05 d4 	. . . 
	call 0c9e1h		;d41d	cd e1 c9 	. . . 
	jp 0d405h		;d420	c3 05 d4 	. . . 
	rst 38h			;d423	ff 	. 
	rst 38h			;d424	ff 	. 
	rst 38h			;d425	ff 	. 
	rst 38h			;d426	ff 	. 
	rst 38h			;d427	ff 	. 
	rst 38h			;d428	ff 	. 
	rst 38h			;d429	ff 	. 
	rst 38h			;d42a	ff 	. 
	rst 38h			;d42b	ff 	. 
	rst 38h			;d42c	ff 	. 
	rst 38h			;d42d	ff 	. 
	rst 38h			;d42e	ff 	. 
	rst 38h			;d42f	ff 	. 
	rst 38h			;d430	ff 	. 
	rst 38h			;d431	ff 	. 
	rst 38h			;d432	ff 	. 
	rst 38h			;d433	ff 	. 
	rst 38h			;d434	ff 	. 
	rst 38h			;d435	ff 	. 
	rst 38h			;d436	ff 	. 
	rst 38h			;d437	ff 	. 
	rst 38h			;d438	ff 	. 
	rst 38h			;d439	ff 	. 
	rst 38h			;d43a	ff 	. 
	rst 38h			;d43b	ff 	. 
	rst 38h			;d43c	ff 	. 
	rst 38h			;d43d	ff 	. 
	rst 38h			;d43e	ff 	. 
	rst 38h			;d43f	ff 	. 
	rst 38h			;d440	ff 	. 
	rst 38h			;d441	ff 	. 
	rst 38h			;d442	ff 	. 
	rst 38h			;d443	ff 	. 
	rst 38h			;d444	ff 	. 
	rst 38h			;d445	ff 	. 
	rst 38h			;d446	ff 	. 
	rst 38h			;d447	ff 	. 
	rst 38h			;d448	ff 	. 
	rst 38h			;d449	ff 	. 
	rst 38h			;d44a	ff 	. 
	rst 38h			;d44b	ff 	. 
	rst 38h			;d44c	ff 	. 
	rst 38h			;d44d	ff 	. 
	rst 38h			;d44e	ff 	. 
	rst 38h			;d44f	ff 	. 
	rst 38h			;d450	ff 	. 
	rst 38h			;d451	ff 	. 
	rst 38h			;d452	ff 	. 
	rst 38h			;d453	ff 	. 
	rst 38h			;d454	ff 	. 
	rst 38h			;d455	ff 	. 
	rst 38h			;d456	ff 	. 
	rst 38h			;d457	ff 	. 
	rst 38h			;d458	ff 	. 
	rst 38h			;d459	ff 	. 
	rst 38h			;d45a	ff 	. 
	rst 38h			;d45b	ff 	. 
	rst 38h			;d45c	ff 	. 
	rst 38h			;d45d	ff 	. 
	rst 38h			;d45e	ff 	. 
	rst 38h			;d45f	ff 	. 
	rst 38h			;d460	ff 	. 
	rst 38h			;d461	ff 	. 
	rst 38h			;d462	ff 	. 
	rst 38h			;d463	ff 	. 
	rst 38h			;d464	ff 	. 
	rst 38h			;d465	ff 	. 
	rst 38h			;d466	ff 	. 
	rst 38h			;d467	ff 	. 
	rst 38h			;d468	ff 	. 
	rst 38h			;d469	ff 	. 
	rst 38h			;d46a	ff 	. 
	rst 38h			;d46b	ff 	. 
	rst 38h			;d46c	ff 	. 
	rst 38h			;d46d	ff 	. 
	rst 38h			;d46e	ff 	. 
	rst 38h			;d46f	ff 	. 
	rst 38h			;d470	ff 	. 
	rst 38h			;d471	ff 	. 
	rst 38h			;d472	ff 	. 
	rst 38h			;d473	ff 	. 
	rst 38h			;d474	ff 	. 
	rst 38h			;d475	ff 	. 
	rst 38h			;d476	ff 	. 
	rst 38h			;d477	ff 	. 
	rst 38h			;d478	ff 	. 
	rst 38h			;d479	ff 	. 
	rst 38h			;d47a	ff 	. 
	rst 38h			;d47b	ff 	. 
	rst 38h			;d47c	ff 	. 
	rst 38h			;d47d	ff 	. 
	rst 38h			;d47e	ff 	. 
	rst 38h			;d47f	ff 	. 
	rst 38h			;d480	ff 	. 
	rst 38h			;d481	ff 	. 
	rst 38h			;d482	ff 	. 
	rst 38h			;d483	ff 	. 
	rst 38h			;d484	ff 	. 
	rst 38h			;d485	ff 	. 
	rst 38h			;d486	ff 	. 
	rst 38h			;d487	ff 	. 
	rst 38h			;d488	ff 	. 
	rst 38h			;d489	ff 	. 
	rst 38h			;d48a	ff 	. 
	rst 38h			;d48b	ff 	. 
	rst 38h			;d48c	ff 	. 
	rst 38h			;d48d	ff 	. 
	rst 38h			;d48e	ff 	. 
	rst 38h			;d48f	ff 	. 
	rst 38h			;d490	ff 	. 
	rst 38h			;d491	ff 	. 
	rst 38h			;d492	ff 	. 
	rst 38h			;d493	ff 	. 
	rst 38h			;d494	ff 	. 
	rst 38h			;d495	ff 	. 
	rst 38h			;d496	ff 	. 
	rst 38h			;d497	ff 	. 
	rst 38h			;d498	ff 	. 
	rst 38h			;d499	ff 	. 
	rst 38h			;d49a	ff 	. 
	rst 38h			;d49b	ff 	. 
	rst 38h			;d49c	ff 	. 
	rst 38h			;d49d	ff 	. 
	rst 38h			;d49e	ff 	. 
	rst 38h			;d49f	ff 	. 
	rst 38h			;d4a0	ff 	. 
	rst 38h			;d4a1	ff 	. 
	rst 38h			;d4a2	ff 	. 
	rst 38h			;d4a3	ff 	. 
	rst 38h			;d4a4	ff 	. 
	rst 38h			;d4a5	ff 	. 
	rst 38h			;d4a6	ff 	. 
	rst 38h			;d4a7	ff 	. 
	rst 38h			;d4a8	ff 	. 
	rst 38h			;d4a9	ff 	. 
	rst 38h			;d4aa	ff 	. 
	rst 38h			;d4ab	ff 	. 
	rst 38h			;d4ac	ff 	. 
	rst 38h			;d4ad	ff 	. 
	rst 38h			;d4ae	ff 	. 
	rst 38h			;d4af	ff 	. 
	rst 38h			;d4b0	ff 	. 
	rst 38h			;d4b1	ff 	. 
	rst 38h			;d4b2	ff 	. 
	rst 38h			;d4b3	ff 	. 
	rst 38h			;d4b4	ff 	. 
	rst 38h			;d4b5	ff 	. 
	rst 38h			;d4b6	ff 	. 
	rst 38h			;d4b7	ff 	. 
	rst 38h			;d4b8	ff 	. 
	rst 38h			;d4b9	ff 	. 
	rst 38h			;d4ba	ff 	. 
	rst 38h			;d4bb	ff 	. 
	rst 38h			;d4bc	ff 	. 
	rst 38h			;d4bd	ff 	. 
	rst 38h			;d4be	ff 	. 
	rst 38h			;d4bf	ff 	. 
	rst 38h			;d4c0	ff 	. 
	rst 38h			;d4c1	ff 	. 
	rst 38h			;d4c2	ff 	. 
	rst 38h			;d4c3	ff 	. 
	rst 38h			;d4c4	ff 	. 
	rst 38h			;d4c5	ff 	. 
	rst 38h			;d4c6	ff 	. 
	rst 38h			;d4c7	ff 	. 
	rst 38h			;d4c8	ff 	. 
	rst 38h			;d4c9	ff 	. 
	rst 38h			;d4ca	ff 	. 
	rst 38h			;d4cb	ff 	. 
	rst 38h			;d4cc	ff 	. 
	rst 38h			;d4cd	ff 	. 
	rst 38h			;d4ce	ff 	. 
	rst 38h			;d4cf	ff 	. 
	rst 38h			;d4d0	ff 	. 
	rst 38h			;d4d1	ff 	. 
	rst 38h			;d4d2	ff 	. 
	rst 38h			;d4d3	ff 	. 
	rst 38h			;d4d4	ff 	. 
	rst 38h			;d4d5	ff 	. 
	rst 38h			;d4d6	ff 	. 
	rst 38h			;d4d7	ff 	. 
	rst 38h			;d4d8	ff 	. 
	rst 38h			;d4d9	ff 	. 
	rst 38h			;d4da	ff 	. 
	rst 38h			;d4db	ff 	. 
	rst 38h			;d4dc	ff 	. 
	rst 38h			;d4dd	ff 	. 
	rst 38h			;d4de	ff 	. 
	rst 38h			;d4df	ff 	. 
	rst 38h			;d4e0	ff 	. 
	rst 38h			;d4e1	ff 	. 
	rst 38h			;d4e2	ff 	. 
	rst 38h			;d4e3	ff 	. 
	rst 38h			;d4e4	ff 	. 
	rst 38h			;d4e5	ff 	. 
	rst 38h			;d4e6	ff 	. 
	rst 38h			;d4e7	ff 	. 
	rst 38h			;d4e8	ff 	. 
	rst 38h			;d4e9	ff 	. 
	rst 38h			;d4ea	ff 	. 
	rst 38h			;d4eb	ff 	. 
	rst 38h			;d4ec	ff 	. 
	rst 38h			;d4ed	ff 	. 
	rst 38h			;d4ee	ff 	. 
	rst 38h			;d4ef	ff 	. 
	rst 38h			;d4f0	ff 	. 
	rst 38h			;d4f1	ff 	. 
	rst 38h			;d4f2	ff 	. 
	rst 38h			;d4f3	ff 	. 
	rst 38h			;d4f4	ff 	. 
	rst 38h			;d4f5	ff 	. 
	rst 38h			;d4f6	ff 	. 
	rst 38h			;d4f7	ff 	. 
	rst 38h			;d4f8	ff 	. 
	rst 38h			;d4f9	ff 	. 
	rst 38h			;d4fa	ff 	. 
	rst 38h			;d4fb	ff 	. 
	rst 38h			;d4fc	ff 	. 
	rst 38h			;d4fd	ff 	. 
	rst 38h			;d4fe	ff 	. 
	rst 38h			;d4ff	ff 	. 
	rst 38h			;d500	ff 	. 
	rst 38h			;d501	ff 	. 
	rst 38h			;d502	ff 	. 
	rst 38h			;d503	ff 	. 
	rst 38h			;d504	ff 	. 
	rst 38h			;d505	ff 	. 
	rst 38h			;d506	ff 	. 
	rst 38h			;d507	ff 	. 
	rst 38h			;d508	ff 	. 
	rst 38h			;d509	ff 	. 
	rst 38h			;d50a	ff 	. 
	rst 38h			;d50b	ff 	. 
	rst 38h			;d50c	ff 	. 
	rst 38h			;d50d	ff 	. 
	rst 38h			;d50e	ff 	. 
	rst 38h			;d50f	ff 	. 
	rst 38h			;d510	ff 	. 
	rst 38h			;d511	ff 	. 
	rst 38h			;d512	ff 	. 
	rst 38h			;d513	ff 	. 
	rst 38h			;d514	ff 	. 
	rst 38h			;d515	ff 	. 
	rst 38h			;d516	ff 	. 
	rst 38h			;d517	ff 	. 
	rst 38h			;d518	ff 	. 
	rst 38h			;d519	ff 	. 
	rst 38h			;d51a	ff 	. 
	rst 38h			;d51b	ff 	. 
	rst 38h			;d51c	ff 	. 
	rst 38h			;d51d	ff 	. 
	rst 38h			;d51e	ff 	. 
	rst 38h			;d51f	ff 	. 
	rst 38h			;d520	ff 	. 
	rst 38h			;d521	ff 	. 
	rst 38h			;d522	ff 	. 
	rst 38h			;d523	ff 	. 
	rst 38h			;d524	ff 	. 
	rst 38h			;d525	ff 	. 
	rst 38h			;d526	ff 	. 
	rst 38h			;d527	ff 	. 
	rst 38h			;d528	ff 	. 
	rst 38h			;d529	ff 	. 
	rst 38h			;d52a	ff 	. 
	rst 38h			;d52b	ff 	. 
	rst 38h			;d52c	ff 	. 
	rst 38h			;d52d	ff 	. 
	rst 38h			;d52e	ff 	. 
	rst 38h			;d52f	ff 	. 
	rst 38h			;d530	ff 	. 
	rst 38h			;d531	ff 	. 
	rst 38h			;d532	ff 	. 
	rst 38h			;d533	ff 	. 
	rst 38h			;d534	ff 	. 
	rst 38h			;d535	ff 	. 
	rst 38h			;d536	ff 	. 
	rst 38h			;d537	ff 	. 
	rst 38h			;d538	ff 	. 
	rst 38h			;d539	ff 	. 
	rst 38h			;d53a	ff 	. 
	rst 38h			;d53b	ff 	. 
	rst 38h			;d53c	ff 	. 
	rst 38h			;d53d	ff 	. 
	rst 38h			;d53e	ff 	. 
	rst 38h			;d53f	ff 	. 
	rst 38h			;d540	ff 	. 
	rst 38h			;d541	ff 	. 
	rst 38h			;d542	ff 	. 
	rst 38h			;d543	ff 	. 
	rst 38h			;d544	ff 	. 
	rst 38h			;d545	ff 	. 
	rst 38h			;d546	ff 	. 
	rst 38h			;d547	ff 	. 
	rst 38h			;d548	ff 	. 
	rst 38h			;d549	ff 	. 
	rst 38h			;d54a	ff 	. 
	rst 38h			;d54b	ff 	. 
	rst 38h			;d54c	ff 	. 
	rst 38h			;d54d	ff 	. 
	rst 38h			;d54e	ff 	. 
	rst 38h			;d54f	ff 	. 
	rst 38h			;d550	ff 	. 
	rst 38h			;d551	ff 	. 
	rst 38h			;d552	ff 	. 
	rst 38h			;d553	ff 	. 
	rst 38h			;d554	ff 	. 
	rst 38h			;d555	ff 	. 
	rst 38h			;d556	ff 	. 
	rst 38h			;d557	ff 	. 
	rst 38h			;d558	ff 	. 
	rst 38h			;d559	ff 	. 
	rst 38h			;d55a	ff 	. 
	rst 38h			;d55b	ff 	. 
	rst 38h			;d55c	ff 	. 
	rst 38h			;d55d	ff 	. 
	rst 38h			;d55e	ff 	. 
	rst 38h			;d55f	ff 	. 
	rst 38h			;d560	ff 	. 
	rst 38h			;d561	ff 	. 
	rst 38h			;d562	ff 	. 
	rst 38h			;d563	ff 	. 
	rst 38h			;d564	ff 	. 
	rst 38h			;d565	ff 	. 
	rst 38h			;d566	ff 	. 
	rst 38h			;d567	ff 	. 
	rst 38h			;d568	ff 	. 
	rst 38h			;d569	ff 	. 
	rst 38h			;d56a	ff 	. 
	rst 38h			;d56b	ff 	. 
	rst 38h			;d56c	ff 	. 
	rst 38h			;d56d	ff 	. 
	rst 38h			;d56e	ff 	. 
	rst 38h			;d56f	ff 	. 
	rst 38h			;d570	ff 	. 
	rst 38h			;d571	ff 	. 
	rst 38h			;d572	ff 	. 
	rst 38h			;d573	ff 	. 
	rst 38h			;d574	ff 	. 
	rst 38h			;d575	ff 	. 
	rst 38h			;d576	ff 	. 
	rst 38h			;d577	ff 	. 
	rst 38h			;d578	ff 	. 
	rst 38h			;d579	ff 	. 
	rst 38h			;d57a	ff 	. 
	rst 38h			;d57b	ff 	. 
	rst 38h			;d57c	ff 	. 
	rst 38h			;d57d	ff 	. 
	rst 38h			;d57e	ff 	. 
	rst 38h			;d57f	ff 	. 
	rst 38h			;d580	ff 	. 
	rst 38h			;d581	ff 	. 
	rst 38h			;d582	ff 	. 
	rst 38h			;d583	ff 	. 
	rst 38h			;d584	ff 	. 
	rst 38h			;d585	ff 	. 
	rst 38h			;d586	ff 	. 
	rst 38h			;d587	ff 	. 
	rst 38h			;d588	ff 	. 
	rst 38h			;d589	ff 	. 
	rst 38h			;d58a	ff 	. 
	rst 38h			;d58b	ff 	. 
	rst 38h			;d58c	ff 	. 
	rst 38h			;d58d	ff 	. 
	rst 38h			;d58e	ff 	. 
	rst 38h			;d58f	ff 	. 
	rst 38h			;d590	ff 	. 
	rst 38h			;d591	ff 	. 
	rst 38h			;d592	ff 	. 
	rst 38h			;d593	ff 	. 
	rst 38h			;d594	ff 	. 
	rst 38h			;d595	ff 	. 
	rst 38h			;d596	ff 	. 
	rst 38h			;d597	ff 	. 
	rst 38h			;d598	ff 	. 
	rst 38h			;d599	ff 	. 
	rst 38h			;d59a	ff 	. 
	rst 38h			;d59b	ff 	. 
	rst 38h			;d59c	ff 	. 
	rst 38h			;d59d	ff 	. 
	rst 38h			;d59e	ff 	. 
	rst 38h			;d59f	ff 	. 
	rst 38h			;d5a0	ff 	. 
	rst 38h			;d5a1	ff 	. 
	rst 38h			;d5a2	ff 	. 
	rst 38h			;d5a3	ff 	. 
	rst 38h			;d5a4	ff 	. 
	rst 38h			;d5a5	ff 	. 
	rst 38h			;d5a6	ff 	. 
	rst 38h			;d5a7	ff 	. 
	rst 38h			;d5a8	ff 	. 
	rst 38h			;d5a9	ff 	. 
	rst 38h			;d5aa	ff 	. 
	rst 38h			;d5ab	ff 	. 
	rst 38h			;d5ac	ff 	. 
	rst 38h			;d5ad	ff 	. 
	rst 38h			;d5ae	ff 	. 
	rst 38h			;d5af	ff 	. 
	rst 38h			;d5b0	ff 	. 
	rst 38h			;d5b1	ff 	. 
	rst 38h			;d5b2	ff 	. 
	rst 38h			;d5b3	ff 	. 
	rst 38h			;d5b4	ff 	. 
	rst 38h			;d5b5	ff 	. 
	rst 38h			;d5b6	ff 	. 
	rst 38h			;d5b7	ff 	. 
	rst 38h			;d5b8	ff 	. 
	rst 38h			;d5b9	ff 	. 
	rst 38h			;d5ba	ff 	. 
	rst 38h			;d5bb	ff 	. 
	rst 38h			;d5bc	ff 	. 
	rst 38h			;d5bd	ff 	. 
	rst 38h			;d5be	ff 	. 
	rst 38h			;d5bf	ff 	. 
	rst 38h			;d5c0	ff 	. 
	rst 38h			;d5c1	ff 	. 
	rst 38h			;d5c2	ff 	. 
	rst 38h			;d5c3	ff 	. 
	rst 38h			;d5c4	ff 	. 
	rst 38h			;d5c5	ff 	. 
	rst 38h			;d5c6	ff 	. 
	rst 38h			;d5c7	ff 	. 
	rst 38h			;d5c8	ff 	. 
	rst 38h			;d5c9	ff 	. 
	rst 38h			;d5ca	ff 	. 
	rst 38h			;d5cb	ff 	. 
	rst 38h			;d5cc	ff 	. 
	rst 38h			;d5cd	ff 	. 
	rst 38h			;d5ce	ff 	. 
	rst 38h			;d5cf	ff 	. 
	rst 38h			;d5d0	ff 	. 
	rst 38h			;d5d1	ff 	. 
	rst 38h			;d5d2	ff 	. 
	rst 38h			;d5d3	ff 	. 
	rst 38h			;d5d4	ff 	. 
	rst 38h			;d5d5	ff 	. 
	rst 38h			;d5d6	ff 	. 
	rst 38h			;d5d7	ff 	. 
	rst 38h			;d5d8	ff 	. 
	rst 38h			;d5d9	ff 	. 
	rst 38h			;d5da	ff 	. 
	rst 38h			;d5db	ff 	. 
	rst 38h			;d5dc	ff 	. 
	rst 38h			;d5dd	ff 	. 
	rst 38h			;d5de	ff 	. 
	rst 38h			;d5df	ff 	. 
	rst 38h			;d5e0	ff 	. 
	rst 38h			;d5e1	ff 	. 
	rst 38h			;d5e2	ff 	. 
	rst 38h			;d5e3	ff 	. 
	rst 38h			;d5e4	ff 	. 
	rst 38h			;d5e5	ff 	. 
	rst 38h			;d5e6	ff 	. 
	rst 38h			;d5e7	ff 	. 
	rst 38h			;d5e8	ff 	. 
	rst 38h			;d5e9	ff 	. 
	rst 38h			;d5ea	ff 	. 
	rst 38h			;d5eb	ff 	. 
	rst 38h			;d5ec	ff 	. 
	rst 38h			;d5ed	ff 	. 
	rst 38h			;d5ee	ff 	. 
	rst 38h			;d5ef	ff 	. 
	rst 38h			;d5f0	ff 	. 
	rst 38h			;d5f1	ff 	. 
	rst 38h			;d5f2	ff 	. 
	rst 38h			;d5f3	ff 	. 
	rst 38h			;d5f4	ff 	. 
	rst 38h			;d5f5	ff 	. 
	rst 38h			;d5f6	ff 	. 
	rst 38h			;d5f7	ff 	. 
	rst 38h			;d5f8	ff 	. 
	rst 38h			;d5f9	ff 	. 
	rst 38h			;d5fa	ff 	. 
	rst 38h			;d5fb	ff 	. 
	rst 38h			;d5fc	ff 	. 
	rst 38h			;d5fd	ff 	. 
	rst 38h			;d5fe	ff 	. 
	rst 38h			;d5ff	ff 	. 
	rst 38h			;d600	ff 	. 
	rst 38h			;d601	ff 	. 
	rst 38h			;d602	ff 	. 
	rst 38h			;d603	ff 	. 
	rst 38h			;d604	ff 	. 
	rst 38h			;d605	ff 	. 
	rst 38h			;d606	ff 	. 
	rst 38h			;d607	ff 	. 
	rst 38h			;d608	ff 	. 
	rst 38h			;d609	ff 	. 
	rst 38h			;d60a	ff 	. 
	rst 38h			;d60b	ff 	. 
	rst 38h			;d60c	ff 	. 
	rst 38h			;d60d	ff 	. 
	rst 38h			;d60e	ff 	. 
	rst 38h			;d60f	ff 	. 
	rst 38h			;d610	ff 	. 
	rst 38h			;d611	ff 	. 
	rst 38h			;d612	ff 	. 
	rst 38h			;d613	ff 	. 
	rst 38h			;d614	ff 	. 
	rst 38h			;d615	ff 	. 
	rst 38h			;d616	ff 	. 
	rst 38h			;d617	ff 	. 
	rst 38h			;d618	ff 	. 
	rst 38h			;d619	ff 	. 
	rst 38h			;d61a	ff 	. 
	rst 38h			;d61b	ff 	. 
	rst 38h			;d61c	ff 	. 
	rst 38h			;d61d	ff 	. 
	rst 38h			;d61e	ff 	. 
	rst 38h			;d61f	ff 	. 
	rst 38h			;d620	ff 	. 
	rst 38h			;d621	ff 	. 
	rst 38h			;d622	ff 	. 
	rst 38h			;d623	ff 	. 
	rst 38h			;d624	ff 	. 
	rst 38h			;d625	ff 	. 
	rst 38h			;d626	ff 	. 
	rst 38h			;d627	ff 	. 
	rst 38h			;d628	ff 	. 
	rst 38h			;d629	ff 	. 
	rst 38h			;d62a	ff 	. 
	rst 38h			;d62b	ff 	. 
	rst 38h			;d62c	ff 	. 
	rst 38h			;d62d	ff 	. 
	rst 38h			;d62e	ff 	. 
	rst 38h			;d62f	ff 	. 
	rst 38h			;d630	ff 	. 
	rst 38h			;d631	ff 	. 
	rst 38h			;d632	ff 	. 
	rst 38h			;d633	ff 	. 
	rst 38h			;d634	ff 	. 
	rst 38h			;d635	ff 	. 
	rst 38h			;d636	ff 	. 
	rst 38h			;d637	ff 	. 
	rst 38h			;d638	ff 	. 
	rst 38h			;d639	ff 	. 
	rst 38h			;d63a	ff 	. 
	rst 38h			;d63b	ff 	. 
	rst 38h			;d63c	ff 	. 
	rst 38h			;d63d	ff 	. 
	rst 38h			;d63e	ff 	. 
	rst 38h			;d63f	ff 	. 
	rst 38h			;d640	ff 	. 
	rst 38h			;d641	ff 	. 
	rst 38h			;d642	ff 	. 
	rst 38h			;d643	ff 	. 
	rst 38h			;d644	ff 	. 
	rst 38h			;d645	ff 	. 
	rst 38h			;d646	ff 	. 
	rst 38h			;d647	ff 	. 
	rst 38h			;d648	ff 	. 
	rst 38h			;d649	ff 	. 
	rst 38h			;d64a	ff 	. 
	rst 38h			;d64b	ff 	. 
	rst 38h			;d64c	ff 	. 
	rst 38h			;d64d	ff 	. 
	rst 38h			;d64e	ff 	. 
	rst 38h			;d64f	ff 	. 
	rst 38h			;d650	ff 	. 
	rst 38h			;d651	ff 	. 
	rst 38h			;d652	ff 	. 
	rst 38h			;d653	ff 	. 
	rst 38h			;d654	ff 	. 
	rst 38h			;d655	ff 	. 
	rst 38h			;d656	ff 	. 
	rst 38h			;d657	ff 	. 
	rst 38h			;d658	ff 	. 
	rst 38h			;d659	ff 	. 
	rst 38h			;d65a	ff 	. 
	rst 38h			;d65b	ff 	. 
	rst 38h			;d65c	ff 	. 
	rst 38h			;d65d	ff 	. 
	rst 38h			;d65e	ff 	. 
	rst 38h			;d65f	ff 	. 
	rst 38h			;d660	ff 	. 
	rst 38h			;d661	ff 	. 
	rst 38h			;d662	ff 	. 
	rst 38h			;d663	ff 	. 
	rst 38h			;d664	ff 	. 
	rst 38h			;d665	ff 	. 
	rst 38h			;d666	ff 	. 
	rst 38h			;d667	ff 	. 
	rst 38h			;d668	ff 	. 
	rst 38h			;d669	ff 	. 
	rst 38h			;d66a	ff 	. 
	rst 38h			;d66b	ff 	. 
	rst 38h			;d66c	ff 	. 
	rst 38h			;d66d	ff 	. 
	rst 38h			;d66e	ff 	. 
	rst 38h			;d66f	ff 	. 
	rst 38h			;d670	ff 	. 
	rst 38h			;d671	ff 	. 
	rst 38h			;d672	ff 	. 
	rst 38h			;d673	ff 	. 
	rst 38h			;d674	ff 	. 
	rst 38h			;d675	ff 	. 
	rst 38h			;d676	ff 	. 
	rst 38h			;d677	ff 	. 
	rst 38h			;d678	ff 	. 
	rst 38h			;d679	ff 	. 
	rst 38h			;d67a	ff 	. 
	rst 38h			;d67b	ff 	. 
	rst 38h			;d67c	ff 	. 
	rst 38h			;d67d	ff 	. 
	rst 38h			;d67e	ff 	. 
	rst 38h			;d67f	ff 	. 
	rst 38h			;d680	ff 	. 
	rst 38h			;d681	ff 	. 
	rst 38h			;d682	ff 	. 
	rst 38h			;d683	ff 	. 
	rst 38h			;d684	ff 	. 
	rst 38h			;d685	ff 	. 
	rst 38h			;d686	ff 	. 
	rst 38h			;d687	ff 	. 
	rst 38h			;d688	ff 	. 
	rst 38h			;d689	ff 	. 
	rst 38h			;d68a	ff 	. 
	rst 38h			;d68b	ff 	. 
	rst 38h			;d68c	ff 	. 
	rst 38h			;d68d	ff 	. 
	rst 38h			;d68e	ff 	. 
	rst 38h			;d68f	ff 	. 
	rst 38h			;d690	ff 	. 
	rst 38h			;d691	ff 	. 
	rst 38h			;d692	ff 	. 
	rst 38h			;d693	ff 	. 
	rst 38h			;d694	ff 	. 
	rst 38h			;d695	ff 	. 
	rst 38h			;d696	ff 	. 
	rst 38h			;d697	ff 	. 
	rst 38h			;d698	ff 	. 
	rst 38h			;d699	ff 	. 
	rst 38h			;d69a	ff 	. 
	rst 38h			;d69b	ff 	. 
	rst 38h			;d69c	ff 	. 
	rst 38h			;d69d	ff 	. 
	rst 38h			;d69e	ff 	. 
	rst 38h			;d69f	ff 	. 
	rst 38h			;d6a0	ff 	. 
	rst 38h			;d6a1	ff 	. 
	rst 38h			;d6a2	ff 	. 
	rst 38h			;d6a3	ff 	. 
	rst 38h			;d6a4	ff 	. 
	rst 38h			;d6a5	ff 	. 
	rst 38h			;d6a6	ff 	. 
	rst 38h			;d6a7	ff 	. 
	rst 38h			;d6a8	ff 	. 
	rst 38h			;d6a9	ff 	. 
	rst 38h			;d6aa	ff 	. 
	rst 38h			;d6ab	ff 	. 
	rst 38h			;d6ac	ff 	. 
	rst 38h			;d6ad	ff 	. 
	rst 38h			;d6ae	ff 	. 
	rst 38h			;d6af	ff 	. 
	rst 38h			;d6b0	ff 	. 
	rst 38h			;d6b1	ff 	. 
	rst 38h			;d6b2	ff 	. 
	rst 38h			;d6b3	ff 	. 
	rst 38h			;d6b4	ff 	. 
	rst 38h			;d6b5	ff 	. 
	rst 38h			;d6b6	ff 	. 
	rst 38h			;d6b7	ff 	. 
	rst 38h			;d6b8	ff 	. 
	rst 38h			;d6b9	ff 	. 
	rst 38h			;d6ba	ff 	. 
	rst 38h			;d6bb	ff 	. 
	rst 38h			;d6bc	ff 	. 
	rst 38h			;d6bd	ff 	. 
	rst 38h			;d6be	ff 	. 
	rst 38h			;d6bf	ff 	. 
	rst 38h			;d6c0	ff 	. 
	rst 38h			;d6c1	ff 	. 
	rst 38h			;d6c2	ff 	. 
	rst 38h			;d6c3	ff 	. 
	rst 38h			;d6c4	ff 	. 
	rst 38h			;d6c5	ff 	. 
	rst 38h			;d6c6	ff 	. 
	rst 38h			;d6c7	ff 	. 
	rst 38h			;d6c8	ff 	. 
	rst 38h			;d6c9	ff 	. 
	rst 38h			;d6ca	ff 	. 
	rst 38h			;d6cb	ff 	. 
	rst 38h			;d6cc	ff 	. 
	rst 38h			;d6cd	ff 	. 
	rst 38h			;d6ce	ff 	. 
	rst 38h			;d6cf	ff 	. 
	rst 38h			;d6d0	ff 	. 
	rst 38h			;d6d1	ff 	. 
	rst 38h			;d6d2	ff 	. 
	rst 38h			;d6d3	ff 	. 
	rst 38h			;d6d4	ff 	. 
	rst 38h			;d6d5	ff 	. 
	rst 38h			;d6d6	ff 	. 
	rst 38h			;d6d7	ff 	. 
	rst 38h			;d6d8	ff 	. 
	rst 38h			;d6d9	ff 	. 
	rst 38h			;d6da	ff 	. 
	rst 38h			;d6db	ff 	. 
	rst 38h			;d6dc	ff 	. 
	rst 38h			;d6dd	ff 	. 
	rst 38h			;d6de	ff 	. 
	rst 38h			;d6df	ff 	. 
	rst 38h			;d6e0	ff 	. 
	rst 38h			;d6e1	ff 	. 
	rst 38h			;d6e2	ff 	. 
	rst 38h			;d6e3	ff 	. 
	rst 38h			;d6e4	ff 	. 
	rst 38h			;d6e5	ff 	. 
	rst 38h			;d6e6	ff 	. 
	rst 38h			;d6e7	ff 	. 
	rst 38h			;d6e8	ff 	. 
	rst 38h			;d6e9	ff 	. 
	rst 38h			;d6ea	ff 	. 
	rst 38h			;d6eb	ff 	. 
	rst 38h			;d6ec	ff 	. 
	rst 38h			;d6ed	ff 	. 
	rst 38h			;d6ee	ff 	. 
	rst 38h			;d6ef	ff 	. 
	rst 38h			;d6f0	ff 	. 
	rst 38h			;d6f1	ff 	. 
	rst 38h			;d6f2	ff 	. 
	rst 38h			;d6f3	ff 	. 
	rst 38h			;d6f4	ff 	. 
	rst 38h			;d6f5	ff 	. 
	rst 38h			;d6f6	ff 	. 
	rst 38h			;d6f7	ff 	. 
	rst 38h			;d6f8	ff 	. 
	rst 38h			;d6f9	ff 	. 
	rst 38h			;d6fa	ff 	. 
	rst 38h			;d6fb	ff 	. 
	rst 38h			;d6fc	ff 	. 
	rst 38h			;d6fd	ff 	. 
	rst 38h			;d6fe	ff 	. 
	rst 38h			;d6ff	ff 	. 
	rst 38h			;d700	ff 	. 
	rst 38h			;d701	ff 	. 
	rst 38h			;d702	ff 	. 
	rst 38h			;d703	ff 	. 
	rst 38h			;d704	ff 	. 
	rst 38h			;d705	ff 	. 
	rst 38h			;d706	ff 	. 
	rst 38h			;d707	ff 	. 
	rst 38h			;d708	ff 	. 
	rst 38h			;d709	ff 	. 
	rst 38h			;d70a	ff 	. 
	rst 38h			;d70b	ff 	. 
	rst 38h			;d70c	ff 	. 
	rst 38h			;d70d	ff 	. 
	rst 38h			;d70e	ff 	. 
	rst 38h			;d70f	ff 	. 
	rst 38h			;d710	ff 	. 
	rst 38h			;d711	ff 	. 
	rst 38h			;d712	ff 	. 
	rst 38h			;d713	ff 	. 
	rst 38h			;d714	ff 	. 
	rst 38h			;d715	ff 	. 
	rst 38h			;d716	ff 	. 
	rst 38h			;d717	ff 	. 
	rst 38h			;d718	ff 	. 
	rst 38h			;d719	ff 	. 
	rst 38h			;d71a	ff 	. 
	rst 38h			;d71b	ff 	. 
	rst 38h			;d71c	ff 	. 
	rst 38h			;d71d	ff 	. 
	rst 38h			;d71e	ff 	. 
	rst 38h			;d71f	ff 	. 
	rst 38h			;d720	ff 	. 
	rst 38h			;d721	ff 	. 
	rst 38h			;d722	ff 	. 
	rst 38h			;d723	ff 	. 
	rst 38h			;d724	ff 	. 
	rst 38h			;d725	ff 	. 
	rst 38h			;d726	ff 	. 
	rst 38h			;d727	ff 	. 
	rst 38h			;d728	ff 	. 
	rst 38h			;d729	ff 	. 
	rst 38h			;d72a	ff 	. 
	rst 38h			;d72b	ff 	. 
	rst 38h			;d72c	ff 	. 
	rst 38h			;d72d	ff 	. 
	rst 38h			;d72e	ff 	. 
	rst 38h			;d72f	ff 	. 
	rst 38h			;d730	ff 	. 
	rst 38h			;d731	ff 	. 
	rst 38h			;d732	ff 	. 
	rst 38h			;d733	ff 	. 
	rst 38h			;d734	ff 	. 
	rst 38h			;d735	ff 	. 
	rst 38h			;d736	ff 	. 
	rst 38h			;d737	ff 	. 
	rst 38h			;d738	ff 	. 
	rst 38h			;d739	ff 	. 
	rst 38h			;d73a	ff 	. 
	rst 38h			;d73b	ff 	. 
	rst 38h			;d73c	ff 	. 
	rst 38h			;d73d	ff 	. 
	rst 38h			;d73e	ff 	. 
	rst 38h			;d73f	ff 	. 
	rst 38h			;d740	ff 	. 
	rst 38h			;d741	ff 	. 
	rst 38h			;d742	ff 	. 
	rst 38h			;d743	ff 	. 
	rst 38h			;d744	ff 	. 
	rst 38h			;d745	ff 	. 
	rst 38h			;d746	ff 	. 
	rst 38h			;d747	ff 	. 
	rst 38h			;d748	ff 	. 
	rst 38h			;d749	ff 	. 
	rst 38h			;d74a	ff 	. 
	rst 38h			;d74b	ff 	. 
	rst 38h			;d74c	ff 	. 
	rst 38h			;d74d	ff 	. 
	rst 38h			;d74e	ff 	. 
	rst 38h			;d74f	ff 	. 
	rst 38h			;d750	ff 	. 
	rst 38h			;d751	ff 	. 
	rst 38h			;d752	ff 	. 
	rst 38h			;d753	ff 	. 
	rst 38h			;d754	ff 	. 
	rst 38h			;d755	ff 	. 
	rst 38h			;d756	ff 	. 
	rst 38h			;d757	ff 	. 
	rst 38h			;d758	ff 	. 
	rst 38h			;d759	ff 	. 
	rst 38h			;d75a	ff 	. 
	rst 38h			;d75b	ff 	. 
	rst 38h			;d75c	ff 	. 
	rst 38h			;d75d	ff 	. 
	rst 38h			;d75e	ff 	. 
	rst 38h			;d75f	ff 	. 
	rst 38h			;d760	ff 	. 
	rst 38h			;d761	ff 	. 
	rst 38h			;d762	ff 	. 
	rst 38h			;d763	ff 	. 
	rst 38h			;d764	ff 	. 
	rst 38h			;d765	ff 	. 
	rst 38h			;d766	ff 	. 
	rst 38h			;d767	ff 	. 
	rst 38h			;d768	ff 	. 
	rst 38h			;d769	ff 	. 
	rst 38h			;d76a	ff 	. 
	rst 38h			;d76b	ff 	. 
	rst 38h			;d76c	ff 	. 
	rst 38h			;d76d	ff 	. 
	rst 38h			;d76e	ff 	. 
	rst 38h			;d76f	ff 	. 
	rst 38h			;d770	ff 	. 
	rst 38h			;d771	ff 	. 
	rst 38h			;d772	ff 	. 
	rst 38h			;d773	ff 	. 
	rst 38h			;d774	ff 	. 
	rst 38h			;d775	ff 	. 
	rst 38h			;d776	ff 	. 
	rst 38h			;d777	ff 	. 
	rst 38h			;d778	ff 	. 
	rst 38h			;d779	ff 	. 
	rst 38h			;d77a	ff 	. 
	rst 38h			;d77b	ff 	. 
	rst 38h			;d77c	ff 	. 
	rst 38h			;d77d	ff 	. 
	rst 38h			;d77e	ff 	. 
	rst 38h			;d77f	ff 	. 
	rst 38h			;d780	ff 	. 
	rst 38h			;d781	ff 	. 
	rst 38h			;d782	ff 	. 
	rst 38h			;d783	ff 	. 
	rst 38h			;d784	ff 	. 
	rst 38h			;d785	ff 	. 
	rst 38h			;d786	ff 	. 
	rst 38h			;d787	ff 	. 
	rst 38h			;d788	ff 	. 
	rst 38h			;d789	ff 	. 
	rst 38h			;d78a	ff 	. 
	rst 38h			;d78b	ff 	. 
	rst 38h			;d78c	ff 	. 
	rst 38h			;d78d	ff 	. 
	rst 38h			;d78e	ff 	. 
	rst 38h			;d78f	ff 	. 
	rst 38h			;d790	ff 	. 
	rst 38h			;d791	ff 	. 
	rst 38h			;d792	ff 	. 
	rst 38h			;d793	ff 	. 
	rst 38h			;d794	ff 	. 
	rst 38h			;d795	ff 	. 
	rst 38h			;d796	ff 	. 
	rst 38h			;d797	ff 	. 
	rst 38h			;d798	ff 	. 
	rst 38h			;d799	ff 	. 
	rst 38h			;d79a	ff 	. 
	rst 38h			;d79b	ff 	. 
	rst 38h			;d79c	ff 	. 
	rst 38h			;d79d	ff 	. 
	rst 38h			;d79e	ff 	. 
	rst 38h			;d79f	ff 	. 
	rst 38h			;d7a0	ff 	. 
	rst 38h			;d7a1	ff 	. 
	rst 38h			;d7a2	ff 	. 
	rst 38h			;d7a3	ff 	. 
	rst 38h			;d7a4	ff 	. 
	rst 38h			;d7a5	ff 	. 
	rst 38h			;d7a6	ff 	. 
	rst 38h			;d7a7	ff 	. 
	rst 38h			;d7a8	ff 	. 
	rst 38h			;d7a9	ff 	. 
	rst 38h			;d7aa	ff 	. 
	rst 38h			;d7ab	ff 	. 
	rst 38h			;d7ac	ff 	. 
	rst 38h			;d7ad	ff 	. 
	rst 38h			;d7ae	ff 	. 
	rst 38h			;d7af	ff 	. 
	rst 38h			;d7b0	ff 	. 
	rst 38h			;d7b1	ff 	. 
	rst 38h			;d7b2	ff 	. 
	rst 38h			;d7b3	ff 	. 
	rst 38h			;d7b4	ff 	. 
	rst 38h			;d7b5	ff 	. 
	rst 38h			;d7b6	ff 	. 
	rst 38h			;d7b7	ff 	. 
	rst 38h			;d7b8	ff 	. 
	rst 38h			;d7b9	ff 	. 
	rst 38h			;d7ba	ff 	. 
	rst 38h			;d7bb	ff 	. 
	rst 38h			;d7bc	ff 	. 
	rst 38h			;d7bd	ff 	. 
	rst 38h			;d7be	ff 	. 
	rst 38h			;d7bf	ff 	. 
	rst 38h			;d7c0	ff 	. 
	rst 38h			;d7c1	ff 	. 
	rst 38h			;d7c2	ff 	. 
	rst 38h			;d7c3	ff 	. 
	rst 38h			;d7c4	ff 	. 
	rst 38h			;d7c5	ff 	. 
	rst 38h			;d7c6	ff 	. 
	rst 38h			;d7c7	ff 	. 
	rst 38h			;d7c8	ff 	. 
	rst 38h			;d7c9	ff 	. 
	rst 38h			;d7ca	ff 	. 
	rst 38h			;d7cb	ff 	. 
	rst 38h			;d7cc	ff 	. 
	rst 38h			;d7cd	ff 	. 
	rst 38h			;d7ce	ff 	. 
	rst 38h			;d7cf	ff 	. 
	rst 38h			;d7d0	ff 	. 
	rst 38h			;d7d1	ff 	. 
	rst 38h			;d7d2	ff 	. 
	rst 38h			;d7d3	ff 	. 
	rst 38h			;d7d4	ff 	. 
	rst 38h			;d7d5	ff 	. 
	rst 38h			;d7d6	ff 	. 
	rst 38h			;d7d7	ff 	. 
	rst 38h			;d7d8	ff 	. 
	rst 38h			;d7d9	ff 	. 
	rst 38h			;d7da	ff 	. 
	rst 38h			;d7db	ff 	. 
	rst 38h			;d7dc	ff 	. 
	rst 38h			;d7dd	ff 	. 
	rst 38h			;d7de	ff 	. 
	rst 38h			;d7df	ff 	. 
	rst 38h			;d7e0	ff 	. 
	rst 38h			;d7e1	ff 	. 
	rst 38h			;d7e2	ff 	. 
	rst 38h			;d7e3	ff 	. 
	rst 38h			;d7e4	ff 	. 
	rst 38h			;d7e5	ff 	. 
	rst 38h			;d7e6	ff 	. 
	rst 38h			;d7e7	ff 	. 
	rst 38h			;d7e8	ff 	. 
	rst 38h			;d7e9	ff 	. 
	rst 38h			;d7ea	ff 	. 
	rst 38h			;d7eb	ff 	. 
	rst 38h			;d7ec	ff 	. 
	rst 38h			;d7ed	ff 	. 
	rst 38h			;d7ee	ff 	. 
	rst 38h			;d7ef	ff 	. 
	rst 38h			;d7f0	ff 	. 
	rst 38h			;d7f1	ff 	. 
	rst 38h			;d7f2	ff 	. 
	rst 38h			;d7f3	ff 	. 
	rst 38h			;d7f4	ff 	. 
	rst 38h			;d7f5	ff 	. 
	rst 38h			;d7f6	ff 	. 
	rst 38h			;d7f7	ff 	. 
	rst 38h			;d7f8	ff 	. 
	rst 38h			;d7f9	ff 	. 
	rst 38h			;d7fa	ff 	. 
	rst 38h			;d7fb	ff 	. 
	rst 38h			;d7fc	ff 	. 
	rst 38h			;d7fd	ff 	. 
	rst 38h			;d7fe	ff 	. 
	rst 38h			;d7ff	ff 	. 
	rst 38h			;d800	ff 	. 
	rst 38h			;d801	ff 	. 
	rst 38h			;d802	ff 	. 
	rst 38h			;d803	ff 	. 
	rst 38h			;d804	ff 	. 
	rst 38h			;d805	ff 	. 
	rst 38h			;d806	ff 	. 
	rst 38h			;d807	ff 	. 
	rst 38h			;d808	ff 	. 
	rst 38h			;d809	ff 	. 
	rst 38h			;d80a	ff 	. 
	rst 38h			;d80b	ff 	. 
	rst 38h			;d80c	ff 	. 
	rst 38h			;d80d	ff 	. 
	rst 38h			;d80e	ff 	. 
	rst 38h			;d80f	ff 	. 
	rst 38h			;d810	ff 	. 
	rst 38h			;d811	ff 	. 
	rst 38h			;d812	ff 	. 
	rst 38h			;d813	ff 	. 
	rst 38h			;d814	ff 	. 
	rst 38h			;d815	ff 	. 
	rst 38h			;d816	ff 	. 
	rst 38h			;d817	ff 	. 
	rst 38h			;d818	ff 	. 
	rst 38h			;d819	ff 	. 
	rst 38h			;d81a	ff 	. 
	rst 38h			;d81b	ff 	. 
	rst 38h			;d81c	ff 	. 
	rst 38h			;d81d	ff 	. 
	rst 38h			;d81e	ff 	. 
	rst 38h			;d81f	ff 	. 
	rst 38h			;d820	ff 	. 
	rst 38h			;d821	ff 	. 
	rst 38h			;d822	ff 	. 
	rst 38h			;d823	ff 	. 
	rst 38h			;d824	ff 	. 
	rst 38h			;d825	ff 	. 
	rst 38h			;d826	ff 	. 
	rst 38h			;d827	ff 	. 
	rst 38h			;d828	ff 	. 
	rst 38h			;d829	ff 	. 
	rst 38h			;d82a	ff 	. 
	rst 38h			;d82b	ff 	. 
	rst 38h			;d82c	ff 	. 
	rst 38h			;d82d	ff 	. 
	rst 38h			;d82e	ff 	. 
	rst 38h			;d82f	ff 	. 
	rst 38h			;d830	ff 	. 
	rst 38h			;d831	ff 	. 
	rst 38h			;d832	ff 	. 
	rst 38h			;d833	ff 	. 
	rst 38h			;d834	ff 	. 
	rst 38h			;d835	ff 	. 
	rst 38h			;d836	ff 	. 
	rst 38h			;d837	ff 	. 
	rst 38h			;d838	ff 	. 
	rst 38h			;d839	ff 	. 
	rst 38h			;d83a	ff 	. 
	rst 38h			;d83b	ff 	. 
	rst 38h			;d83c	ff 	. 
	rst 38h			;d83d	ff 	. 
	rst 38h			;d83e	ff 	. 
	rst 38h			;d83f	ff 	. 
	rst 38h			;d840	ff 	. 
	rst 38h			;d841	ff 	. 
	rst 38h			;d842	ff 	. 
	rst 38h			;d843	ff 	. 
	rst 38h			;d844	ff 	. 
	rst 38h			;d845	ff 	. 
	rst 38h			;d846	ff 	. 
	rst 38h			;d847	ff 	. 
	rst 38h			;d848	ff 	. 
	rst 38h			;d849	ff 	. 
	rst 38h			;d84a	ff 	. 
	rst 38h			;d84b	ff 	. 
	rst 38h			;d84c	ff 	. 
	rst 38h			;d84d	ff 	. 
	rst 38h			;d84e	ff 	. 
	rst 38h			;d84f	ff 	. 
	rst 38h			;d850	ff 	. 
	rst 38h			;d851	ff 	. 
	rst 38h			;d852	ff 	. 
	rst 38h			;d853	ff 	. 
	rst 38h			;d854	ff 	. 
	rst 38h			;d855	ff 	. 
	rst 38h			;d856	ff 	. 
	rst 38h			;d857	ff 	. 
	rst 38h			;d858	ff 	. 
	rst 38h			;d859	ff 	. 
	rst 38h			;d85a	ff 	. 
	rst 38h			;d85b	ff 	. 
	rst 38h			;d85c	ff 	. 
	rst 38h			;d85d	ff 	. 
	rst 38h			;d85e	ff 	. 
	rst 38h			;d85f	ff 	. 
	rst 38h			;d860	ff 	. 
	rst 38h			;d861	ff 	. 
	rst 38h			;d862	ff 	. 
	rst 38h			;d863	ff 	. 
	rst 38h			;d864	ff 	. 
	rst 38h			;d865	ff 	. 
	rst 38h			;d866	ff 	. 
	rst 38h			;d867	ff 	. 
	rst 38h			;d868	ff 	. 
	rst 38h			;d869	ff 	. 
	rst 38h			;d86a	ff 	. 
	rst 38h			;d86b	ff 	. 
	rst 38h			;d86c	ff 	. 
	rst 38h			;d86d	ff 	. 
	rst 38h			;d86e	ff 	. 
	rst 38h			;d86f	ff 	. 
	rst 38h			;d870	ff 	. 
	rst 38h			;d871	ff 	. 
	rst 38h			;d872	ff 	. 
	rst 38h			;d873	ff 	. 
	rst 38h			;d874	ff 	. 
	rst 38h			;d875	ff 	. 
	rst 38h			;d876	ff 	. 
	rst 38h			;d877	ff 	. 
	rst 38h			;d878	ff 	. 
	rst 38h			;d879	ff 	. 
	rst 38h			;d87a	ff 	. 
	rst 38h			;d87b	ff 	. 
	rst 38h			;d87c	ff 	. 
	rst 38h			;d87d	ff 	. 
	rst 38h			;d87e	ff 	. 
	rst 38h			;d87f	ff 	. 
	rst 38h			;d880	ff 	. 
	rst 38h			;d881	ff 	. 
	rst 38h			;d882	ff 	. 
	rst 38h			;d883	ff 	. 
	rst 38h			;d884	ff 	. 
	rst 38h			;d885	ff 	. 
	rst 38h			;d886	ff 	. 
	rst 38h			;d887	ff 	. 
	rst 38h			;d888	ff 	. 
	rst 38h			;d889	ff 	. 
	rst 38h			;d88a	ff 	. 
	rst 38h			;d88b	ff 	. 
	rst 38h			;d88c	ff 	. 
	rst 38h			;d88d	ff 	. 
	rst 38h			;d88e	ff 	. 
	rst 38h			;d88f	ff 	. 
	rst 38h			;d890	ff 	. 
	rst 38h			;d891	ff 	. 
	rst 38h			;d892	ff 	. 
	rst 38h			;d893	ff 	. 
	rst 38h			;d894	ff 	. 
	rst 38h			;d895	ff 	. 
	rst 38h			;d896	ff 	. 
	rst 38h			;d897	ff 	. 
	rst 38h			;d898	ff 	. 
	rst 38h			;d899	ff 	. 
	rst 38h			;d89a	ff 	. 
	rst 38h			;d89b	ff 	. 
	rst 38h			;d89c	ff 	. 
	rst 38h			;d89d	ff 	. 
	rst 38h			;d89e	ff 	. 
	rst 38h			;d89f	ff 	. 
	rst 38h			;d8a0	ff 	. 
	rst 38h			;d8a1	ff 	. 
	rst 38h			;d8a2	ff 	. 
	rst 38h			;d8a3	ff 	. 
	rst 38h			;d8a4	ff 	. 
	rst 38h			;d8a5	ff 	. 
	rst 38h			;d8a6	ff 	. 
	rst 38h			;d8a7	ff 	. 
	rst 38h			;d8a8	ff 	. 
	rst 38h			;d8a9	ff 	. 
	rst 38h			;d8aa	ff 	. 
	rst 38h			;d8ab	ff 	. 
	rst 38h			;d8ac	ff 	. 
	rst 38h			;d8ad	ff 	. 
	rst 38h			;d8ae	ff 	. 
	rst 38h			;d8af	ff 	. 
	rst 38h			;d8b0	ff 	. 
	rst 38h			;d8b1	ff 	. 
	rst 38h			;d8b2	ff 	. 
	rst 38h			;d8b3	ff 	. 
	rst 38h			;d8b4	ff 	. 
	rst 38h			;d8b5	ff 	. 
	rst 38h			;d8b6	ff 	. 
	rst 38h			;d8b7	ff 	. 
	rst 38h			;d8b8	ff 	. 
	rst 38h			;d8b9	ff 	. 
	rst 38h			;d8ba	ff 	. 
	rst 38h			;d8bb	ff 	. 
	rst 38h			;d8bc	ff 	. 
	rst 38h			;d8bd	ff 	. 
	rst 38h			;d8be	ff 	. 
	rst 38h			;d8bf	ff 	. 
	rst 38h			;d8c0	ff 	. 
	rst 38h			;d8c1	ff 	. 
	rst 38h			;d8c2	ff 	. 
	rst 38h			;d8c3	ff 	. 
	rst 38h			;d8c4	ff 	. 
	rst 38h			;d8c5	ff 	. 
	rst 38h			;d8c6	ff 	. 
	rst 38h			;d8c7	ff 	. 
	rst 38h			;d8c8	ff 	. 
	rst 38h			;d8c9	ff 	. 
	rst 38h			;d8ca	ff 	. 
	rst 38h			;d8cb	ff 	. 
	rst 38h			;d8cc	ff 	. 
	rst 38h			;d8cd	ff 	. 
	rst 38h			;d8ce	ff 	. 
	rst 38h			;d8cf	ff 	. 
	rst 38h			;d8d0	ff 	. 
	rst 38h			;d8d1	ff 	. 
	rst 38h			;d8d2	ff 	. 
	rst 38h			;d8d3	ff 	. 
	rst 38h			;d8d4	ff 	. 
	rst 38h			;d8d5	ff 	. 
	rst 38h			;d8d6	ff 	. 
	rst 38h			;d8d7	ff 	. 
	rst 38h			;d8d8	ff 	. 
	rst 38h			;d8d9	ff 	. 
	rst 38h			;d8da	ff 	. 
	rst 38h			;d8db	ff 	. 
	rst 38h			;d8dc	ff 	. 
	rst 38h			;d8dd	ff 	. 
	rst 38h			;d8de	ff 	. 
	rst 38h			;d8df	ff 	. 
	rst 38h			;d8e0	ff 	. 
	rst 38h			;d8e1	ff 	. 
	rst 38h			;d8e2	ff 	. 
	rst 38h			;d8e3	ff 	. 
	rst 38h			;d8e4	ff 	. 
	rst 38h			;d8e5	ff 	. 
	rst 38h			;d8e6	ff 	. 
	rst 38h			;d8e7	ff 	. 
	rst 38h			;d8e8	ff 	. 
	rst 38h			;d8e9	ff 	. 
	rst 38h			;d8ea	ff 	. 
	rst 38h			;d8eb	ff 	. 
	rst 38h			;d8ec	ff 	. 
	rst 38h			;d8ed	ff 	. 
	rst 38h			;d8ee	ff 	. 
	rst 38h			;d8ef	ff 	. 
	rst 38h			;d8f0	ff 	. 
	rst 38h			;d8f1	ff 	. 
	rst 38h			;d8f2	ff 	. 
	rst 38h			;d8f3	ff 	. 
	rst 38h			;d8f4	ff 	. 
	rst 38h			;d8f5	ff 	. 
	rst 38h			;d8f6	ff 	. 
	rst 38h			;d8f7	ff 	. 
	rst 38h			;d8f8	ff 	. 
	rst 38h			;d8f9	ff 	. 
	rst 38h			;d8fa	ff 	. 
	rst 38h			;d8fb	ff 	. 
	rst 38h			;d8fc	ff 	. 
	rst 38h			;d8fd	ff 	. 
	rst 38h			;d8fe	ff 	. 
	rst 38h			;d8ff	ff 	. 
	rst 38h			;d900	ff 	. 
	rst 38h			;d901	ff 	. 
	rst 38h			;d902	ff 	. 
	rst 38h			;d903	ff 	. 
	rst 38h			;d904	ff 	. 
	rst 38h			;d905	ff 	. 
	rst 38h			;d906	ff 	. 
	rst 38h			;d907	ff 	. 
	rst 38h			;d908	ff 	. 
	rst 38h			;d909	ff 	. 
	rst 38h			;d90a	ff 	. 
	rst 38h			;d90b	ff 	. 
	rst 38h			;d90c	ff 	. 
	rst 38h			;d90d	ff 	. 
	rst 38h			;d90e	ff 	. 
	rst 38h			;d90f	ff 	. 
	rst 38h			;d910	ff 	. 
	rst 38h			;d911	ff 	. 
	rst 38h			;d912	ff 	. 
	rst 38h			;d913	ff 	. 
	rst 38h			;d914	ff 	. 
	rst 38h			;d915	ff 	. 
	rst 38h			;d916	ff 	. 
	rst 38h			;d917	ff 	. 
	rst 38h			;d918	ff 	. 
	rst 38h			;d919	ff 	. 
	rst 38h			;d91a	ff 	. 
	rst 38h			;d91b	ff 	. 
	rst 38h			;d91c	ff 	. 
	rst 38h			;d91d	ff 	. 
	rst 38h			;d91e	ff 	. 
	rst 38h			;d91f	ff 	. 
	rst 38h			;d920	ff 	. 
	rst 38h			;d921	ff 	. 
	rst 38h			;d922	ff 	. 
	rst 38h			;d923	ff 	. 
	rst 38h			;d924	ff 	. 
	rst 38h			;d925	ff 	. 
	rst 38h			;d926	ff 	. 
	rst 38h			;d927	ff 	. 
	rst 38h			;d928	ff 	. 
	rst 38h			;d929	ff 	. 
	rst 38h			;d92a	ff 	. 
	rst 38h			;d92b	ff 	. 
	rst 38h			;d92c	ff 	. 
	rst 38h			;d92d	ff 	. 
	rst 38h			;d92e	ff 	. 
	rst 38h			;d92f	ff 	. 
	rst 38h			;d930	ff 	. 
	rst 38h			;d931	ff 	. 
	rst 38h			;d932	ff 	. 
	rst 38h			;d933	ff 	. 
	rst 38h			;d934	ff 	. 
	rst 38h			;d935	ff 	. 
	rst 38h			;d936	ff 	. 
	rst 38h			;d937	ff 	. 
	rst 38h			;d938	ff 	. 
	rst 38h			;d939	ff 	. 
	rst 38h			;d93a	ff 	. 
	rst 38h			;d93b	ff 	. 
	rst 38h			;d93c	ff 	. 
	rst 38h			;d93d	ff 	. 
	rst 38h			;d93e	ff 	. 
	rst 38h			;d93f	ff 	. 
	rst 38h			;d940	ff 	. 
	rst 38h			;d941	ff 	. 
	rst 38h			;d942	ff 	. 
	rst 38h			;d943	ff 	. 
	rst 38h			;d944	ff 	. 
	rst 38h			;d945	ff 	. 
	rst 38h			;d946	ff 	. 
	rst 38h			;d947	ff 	. 
	rst 38h			;d948	ff 	. 
	rst 38h			;d949	ff 	. 
	rst 38h			;d94a	ff 	. 
	rst 38h			;d94b	ff 	. 
	rst 38h			;d94c	ff 	. 
	rst 38h			;d94d	ff 	. 
	rst 38h			;d94e	ff 	. 
	rst 38h			;d94f	ff 	. 
	rst 38h			;d950	ff 	. 
	rst 38h			;d951	ff 	. 
	rst 38h			;d952	ff 	. 
	rst 38h			;d953	ff 	. 
	rst 38h			;d954	ff 	. 
	rst 38h			;d955	ff 	. 
	rst 38h			;d956	ff 	. 
	rst 38h			;d957	ff 	. 
	rst 38h			;d958	ff 	. 
	rst 38h			;d959	ff 	. 
	rst 38h			;d95a	ff 	. 
	rst 38h			;d95b	ff 	. 
	rst 38h			;d95c	ff 	. 
	rst 38h			;d95d	ff 	. 
	rst 38h			;d95e	ff 	. 
	rst 38h			;d95f	ff 	. 
	rst 38h			;d960	ff 	. 
	rst 38h			;d961	ff 	. 
	rst 38h			;d962	ff 	. 
	rst 38h			;d963	ff 	. 
	rst 38h			;d964	ff 	. 
	rst 38h			;d965	ff 	. 
	rst 38h			;d966	ff 	. 
	rst 38h			;d967	ff 	. 
	rst 38h			;d968	ff 	. 
	rst 38h			;d969	ff 	. 
	rst 38h			;d96a	ff 	. 
	rst 38h			;d96b	ff 	. 
	rst 38h			;d96c	ff 	. 
	rst 38h			;d96d	ff 	. 
	rst 38h			;d96e	ff 	. 
	rst 38h			;d96f	ff 	. 
	rst 38h			;d970	ff 	. 
	rst 38h			;d971	ff 	. 
	rst 38h			;d972	ff 	. 
	rst 38h			;d973	ff 	. 
	rst 38h			;d974	ff 	. 
	rst 38h			;d975	ff 	. 
	rst 38h			;d976	ff 	. 
	rst 38h			;d977	ff 	. 
	rst 38h			;d978	ff 	. 
	rst 38h			;d979	ff 	. 
	rst 38h			;d97a	ff 	. 
	rst 38h			;d97b	ff 	. 
	rst 38h			;d97c	ff 	. 
	rst 38h			;d97d	ff 	. 
	rst 38h			;d97e	ff 	. 
	rst 38h			;d97f	ff 	. 
	rst 38h			;d980	ff 	. 
	rst 38h			;d981	ff 	. 
	rst 38h			;d982	ff 	. 
	rst 38h			;d983	ff 	. 
	rst 38h			;d984	ff 	. 
	rst 38h			;d985	ff 	. 
	rst 38h			;d986	ff 	. 
	rst 38h			;d987	ff 	. 
	rst 38h			;d988	ff 	. 
	rst 38h			;d989	ff 	. 
	rst 38h			;d98a	ff 	. 
	rst 38h			;d98b	ff 	. 
	rst 38h			;d98c	ff 	. 
	rst 38h			;d98d	ff 	. 
	rst 38h			;d98e	ff 	. 
	rst 38h			;d98f	ff 	. 
	rst 38h			;d990	ff 	. 
	rst 38h			;d991	ff 	. 
	rst 38h			;d992	ff 	. 
	rst 38h			;d993	ff 	. 
	rst 38h			;d994	ff 	. 
	rst 38h			;d995	ff 	. 
	rst 38h			;d996	ff 	. 
	rst 38h			;d997	ff 	. 
	rst 38h			;d998	ff 	. 
	rst 38h			;d999	ff 	. 
	rst 38h			;d99a	ff 	. 
	rst 38h			;d99b	ff 	. 
	rst 38h			;d99c	ff 	. 
	rst 38h			;d99d	ff 	. 
	rst 38h			;d99e	ff 	. 
	rst 38h			;d99f	ff 	. 
	rst 38h			;d9a0	ff 	. 
	rst 38h			;d9a1	ff 	. 
	rst 38h			;d9a2	ff 	. 
	rst 38h			;d9a3	ff 	. 
	rst 38h			;d9a4	ff 	. 
	rst 38h			;d9a5	ff 	. 
	rst 38h			;d9a6	ff 	. 
	rst 38h			;d9a7	ff 	. 
	rst 38h			;d9a8	ff 	. 
	rst 38h			;d9a9	ff 	. 
	rst 38h			;d9aa	ff 	. 
	rst 38h			;d9ab	ff 	. 
	rst 38h			;d9ac	ff 	. 
	rst 38h			;d9ad	ff 	. 
	rst 38h			;d9ae	ff 	. 
	rst 38h			;d9af	ff 	. 
	rst 38h			;d9b0	ff 	. 
	rst 38h			;d9b1	ff 	. 
	rst 38h			;d9b2	ff 	. 
	rst 38h			;d9b3	ff 	. 
	rst 38h			;d9b4	ff 	. 
	rst 38h			;d9b5	ff 	. 
	rst 38h			;d9b6	ff 	. 
	rst 38h			;d9b7	ff 	. 
	rst 38h			;d9b8	ff 	. 
	rst 38h			;d9b9	ff 	. 
	rst 38h			;d9ba	ff 	. 
	rst 38h			;d9bb	ff 	. 
	rst 38h			;d9bc	ff 	. 
	rst 38h			;d9bd	ff 	. 
	rst 38h			;d9be	ff 	. 
	rst 38h			;d9bf	ff 	. 
	rst 38h			;d9c0	ff 	. 
	rst 38h			;d9c1	ff 	. 
	rst 38h			;d9c2	ff 	. 
	rst 38h			;d9c3	ff 	. 
	rst 38h			;d9c4	ff 	. 
	rst 38h			;d9c5	ff 	. 
	rst 38h			;d9c6	ff 	. 
	rst 38h			;d9c7	ff 	. 
	rst 38h			;d9c8	ff 	. 
	rst 38h			;d9c9	ff 	. 
	rst 38h			;d9ca	ff 	. 
	rst 38h			;d9cb	ff 	. 
	rst 38h			;d9cc	ff 	. 
	rst 38h			;d9cd	ff 	. 
	rst 38h			;d9ce	ff 	. 
	rst 38h			;d9cf	ff 	. 
	rst 38h			;d9d0	ff 	. 
	rst 38h			;d9d1	ff 	. 
	rst 38h			;d9d2	ff 	. 
	rst 38h			;d9d3	ff 	. 
	rst 38h			;d9d4	ff 	. 
	rst 38h			;d9d5	ff 	. 
	rst 38h			;d9d6	ff 	. 
	rst 38h			;d9d7	ff 	. 
	rst 38h			;d9d8	ff 	. 
	rst 38h			;d9d9	ff 	. 
	rst 38h			;d9da	ff 	. 
	rst 38h			;d9db	ff 	. 
	rst 38h			;d9dc	ff 	. 
	rst 38h			;d9dd	ff 	. 
	rst 38h			;d9de	ff 	. 
	rst 38h			;d9df	ff 	. 
	rst 38h			;d9e0	ff 	. 
	rst 38h			;d9e1	ff 	. 
	rst 38h			;d9e2	ff 	. 
	rst 38h			;d9e3	ff 	. 
	rst 38h			;d9e4	ff 	. 
	rst 38h			;d9e5	ff 	. 
	rst 38h			;d9e6	ff 	. 
	rst 38h			;d9e7	ff 	. 
	rst 38h			;d9e8	ff 	. 
	rst 38h			;d9e9	ff 	. 
	rst 38h			;d9ea	ff 	. 
	rst 38h			;d9eb	ff 	. 
	rst 38h			;d9ec	ff 	. 
	rst 38h			;d9ed	ff 	. 
	rst 38h			;d9ee	ff 	. 
	rst 38h			;d9ef	ff 	. 
	rst 38h			;d9f0	ff 	. 
	rst 38h			;d9f1	ff 	. 
	rst 38h			;d9f2	ff 	. 
	rst 38h			;d9f3	ff 	. 
	rst 38h			;d9f4	ff 	. 
	rst 38h			;d9f5	ff 	. 
	rst 38h			;d9f6	ff 	. 
	rst 38h			;d9f7	ff 	. 
	rst 38h			;d9f8	ff 	. 
	rst 38h			;d9f9	ff 	. 
	rst 38h			;d9fa	ff 	. 
	rst 38h			;d9fb	ff 	. 
	rst 38h			;d9fc	ff 	. 
	rst 38h			;d9fd	ff 	. 
	rst 38h			;d9fe	ff 	. 
	rst 38h			;d9ff	ff 	. 
	rst 38h			;da00	ff 	. 
	rst 38h			;da01	ff 	. 
	rst 38h			;da02	ff 	. 
	rst 38h			;da03	ff 	. 
	rst 38h			;da04	ff 	. 
	rst 38h			;da05	ff 	. 
	rst 38h			;da06	ff 	. 
	rst 38h			;da07	ff 	. 
	rst 38h			;da08	ff 	. 
	rst 38h			;da09	ff 	. 
	rst 38h			;da0a	ff 	. 
	rst 38h			;da0b	ff 	. 
	rst 38h			;da0c	ff 	. 
	rst 38h			;da0d	ff 	. 
	rst 38h			;da0e	ff 	. 
	rst 38h			;da0f	ff 	. 
	rst 38h			;da10	ff 	. 
	rst 38h			;da11	ff 	. 
	rst 38h			;da12	ff 	. 
	rst 38h			;da13	ff 	. 
	rst 38h			;da14	ff 	. 
	rst 38h			;da15	ff 	. 
	rst 38h			;da16	ff 	. 
	rst 38h			;da17	ff 	. 
	rst 38h			;da18	ff 	. 
	rst 38h			;da19	ff 	. 
	rst 38h			;da1a	ff 	. 
	rst 38h			;da1b	ff 	. 
	rst 38h			;da1c	ff 	. 
	rst 38h			;da1d	ff 	. 
	rst 38h			;da1e	ff 	. 
	rst 38h			;da1f	ff 	. 
	rst 38h			;da20	ff 	. 
	rst 38h			;da21	ff 	. 
	rst 38h			;da22	ff 	. 
	rst 38h			;da23	ff 	. 
	rst 38h			;da24	ff 	. 
	rst 38h			;da25	ff 	. 
	rst 38h			;da26	ff 	. 
	rst 38h			;da27	ff 	. 
	rst 38h			;da28	ff 	. 
	rst 38h			;da29	ff 	. 
	rst 38h			;da2a	ff 	. 
	rst 38h			;da2b	ff 	. 
	rst 38h			;da2c	ff 	. 
	rst 38h			;da2d	ff 	. 
	rst 38h			;da2e	ff 	. 
	rst 38h			;da2f	ff 	. 
	rst 38h			;da30	ff 	. 
	rst 38h			;da31	ff 	. 
	rst 38h			;da32	ff 	. 
	rst 38h			;da33	ff 	. 
	rst 38h			;da34	ff 	. 
	rst 38h			;da35	ff 	. 
	rst 38h			;da36	ff 	. 
	rst 38h			;da37	ff 	. 
	rst 38h			;da38	ff 	. 
	rst 38h			;da39	ff 	. 
	rst 38h			;da3a	ff 	. 
	rst 38h			;da3b	ff 	. 
	rst 38h			;da3c	ff 	. 
	rst 38h			;da3d	ff 	. 
	rst 38h			;da3e	ff 	. 
	rst 38h			;da3f	ff 	. 
	rst 38h			;da40	ff 	. 
	rst 38h			;da41	ff 	. 
	rst 38h			;da42	ff 	. 
	rst 38h			;da43	ff 	. 
	rst 38h			;da44	ff 	. 
	rst 38h			;da45	ff 	. 
	rst 38h			;da46	ff 	. 
	rst 38h			;da47	ff 	. 
	rst 38h			;da48	ff 	. 
	rst 38h			;da49	ff 	. 
	rst 38h			;da4a	ff 	. 
	rst 38h			;da4b	ff 	. 
	rst 38h			;da4c	ff 	. 
	rst 38h			;da4d	ff 	. 
	rst 38h			;da4e	ff 	. 
	rst 38h			;da4f	ff 	. 
	rst 38h			;da50	ff 	. 
	rst 38h			;da51	ff 	. 
	rst 38h			;da52	ff 	. 
	rst 38h			;da53	ff 	. 
	rst 38h			;da54	ff 	. 
	rst 38h			;da55	ff 	. 
	rst 38h			;da56	ff 	. 
	rst 38h			;da57	ff 	. 
	rst 38h			;da58	ff 	. 
	rst 38h			;da59	ff 	. 
	rst 38h			;da5a	ff 	. 
	rst 38h			;da5b	ff 	. 
	rst 38h			;da5c	ff 	. 
	rst 38h			;da5d	ff 	. 
	rst 38h			;da5e	ff 	. 
	rst 38h			;da5f	ff 	. 
	rst 38h			;da60	ff 	. 
	rst 38h			;da61	ff 	. 
	rst 38h			;da62	ff 	. 
	rst 38h			;da63	ff 	. 
	rst 38h			;da64	ff 	. 
	rst 38h			;da65	ff 	. 
	rst 38h			;da66	ff 	. 
	rst 38h			;da67	ff 	. 
	rst 38h			;da68	ff 	. 
	rst 38h			;da69	ff 	. 
	rst 38h			;da6a	ff 	. 
	rst 38h			;da6b	ff 	. 
	rst 38h			;da6c	ff 	. 
	rst 38h			;da6d	ff 	. 
	rst 38h			;da6e	ff 	. 
	rst 38h			;da6f	ff 	. 
	rst 38h			;da70	ff 	. 
	rst 38h			;da71	ff 	. 
	rst 38h			;da72	ff 	. 
	rst 38h			;da73	ff 	. 
	rst 38h			;da74	ff 	. 
	rst 38h			;da75	ff 	. 
	rst 38h			;da76	ff 	. 
	rst 38h			;da77	ff 	. 
	rst 38h			;da78	ff 	. 
	rst 38h			;da79	ff 	. 
	rst 38h			;da7a	ff 	. 
	rst 38h			;da7b	ff 	. 
	rst 38h			;da7c	ff 	. 
	rst 38h			;da7d	ff 	. 
	rst 38h			;da7e	ff 	. 
	rst 38h			;da7f	ff 	. 
	rst 38h			;da80	ff 	. 
	rst 38h			;da81	ff 	. 
	rst 38h			;da82	ff 	. 
	rst 38h			;da83	ff 	. 
	rst 38h			;da84	ff 	. 
	rst 38h			;da85	ff 	. 
	rst 38h			;da86	ff 	. 
	rst 38h			;da87	ff 	. 
	rst 38h			;da88	ff 	. 
	rst 38h			;da89	ff 	. 
	rst 38h			;da8a	ff 	. 
	rst 38h			;da8b	ff 	. 
	rst 38h			;da8c	ff 	. 
	rst 38h			;da8d	ff 	. 
	rst 38h			;da8e	ff 	. 
	rst 38h			;da8f	ff 	. 
	rst 38h			;da90	ff 	. 
	rst 38h			;da91	ff 	. 
	rst 38h			;da92	ff 	. 
	rst 38h			;da93	ff 	. 
	rst 38h			;da94	ff 	. 
	rst 38h			;da95	ff 	. 
	rst 38h			;da96	ff 	. 
	rst 38h			;da97	ff 	. 
	rst 38h			;da98	ff 	. 
	rst 38h			;da99	ff 	. 
	rst 38h			;da9a	ff 	. 
	rst 38h			;da9b	ff 	. 
	rst 38h			;da9c	ff 	. 
	rst 38h			;da9d	ff 	. 
	rst 38h			;da9e	ff 	. 
	rst 38h			;da9f	ff 	. 
	rst 38h			;daa0	ff 	. 
	rst 38h			;daa1	ff 	. 
	rst 38h			;daa2	ff 	. 
	rst 38h			;daa3	ff 	. 
	rst 38h			;daa4	ff 	. 
	rst 38h			;daa5	ff 	. 
	rst 38h			;daa6	ff 	. 
	rst 38h			;daa7	ff 	. 
	rst 38h			;daa8	ff 	. 
	rst 38h			;daa9	ff 	. 
	rst 38h			;daaa	ff 	. 
	rst 38h			;daab	ff 	. 
	rst 38h			;daac	ff 	. 
	rst 38h			;daad	ff 	. 
	rst 38h			;daae	ff 	. 
	rst 38h			;daaf	ff 	. 
	rst 38h			;dab0	ff 	. 
	rst 38h			;dab1	ff 	. 
	rst 38h			;dab2	ff 	. 
	rst 38h			;dab3	ff 	. 
	rst 38h			;dab4	ff 	. 
	rst 38h			;dab5	ff 	. 
	rst 38h			;dab6	ff 	. 
	rst 38h			;dab7	ff 	. 
	rst 38h			;dab8	ff 	. 
	rst 38h			;dab9	ff 	. 
	rst 38h			;daba	ff 	. 
	rst 38h			;dabb	ff 	. 
	rst 38h			;dabc	ff 	. 
	rst 38h			;dabd	ff 	. 
	rst 38h			;dabe	ff 	. 
	rst 38h			;dabf	ff 	. 
	rst 38h			;dac0	ff 	. 
	rst 38h			;dac1	ff 	. 
	rst 38h			;dac2	ff 	. 
	rst 38h			;dac3	ff 	. 
	rst 38h			;dac4	ff 	. 
	rst 38h			;dac5	ff 	. 
	rst 38h			;dac6	ff 	. 
	rst 38h			;dac7	ff 	. 
	rst 38h			;dac8	ff 	. 
	rst 38h			;dac9	ff 	. 
	rst 38h			;daca	ff 	. 
	rst 38h			;dacb	ff 	. 
	rst 38h			;dacc	ff 	. 
	rst 38h			;dacd	ff 	. 
	rst 38h			;dace	ff 	. 
	rst 38h			;dacf	ff 	. 
	rst 38h			;dad0	ff 	. 
	rst 38h			;dad1	ff 	. 
	rst 38h			;dad2	ff 	. 
	rst 38h			;dad3	ff 	. 
	rst 38h			;dad4	ff 	. 
	rst 38h			;dad5	ff 	. 
	rst 38h			;dad6	ff 	. 
	rst 38h			;dad7	ff 	. 
	rst 38h			;dad8	ff 	. 
	rst 38h			;dad9	ff 	. 
	rst 38h			;dada	ff 	. 
	rst 38h			;dadb	ff 	. 
	rst 38h			;dadc	ff 	. 
	rst 38h			;dadd	ff 	. 
	rst 38h			;dade	ff 	. 
	rst 38h			;dadf	ff 	. 
	rst 38h			;dae0	ff 	. 
	rst 38h			;dae1	ff 	. 
	rst 38h			;dae2	ff 	. 
	rst 38h			;dae3	ff 	. 
	rst 38h			;dae4	ff 	. 
	rst 38h			;dae5	ff 	. 
	rst 38h			;dae6	ff 	. 
	rst 38h			;dae7	ff 	. 
	rst 38h			;dae8	ff 	. 
	rst 38h			;dae9	ff 	. 
	rst 38h			;daea	ff 	. 
	rst 38h			;daeb	ff 	. 
	rst 38h			;daec	ff 	. 
	rst 38h			;daed	ff 	. 
	rst 38h			;daee	ff 	. 
	rst 38h			;daef	ff 	. 
	rst 38h			;daf0	ff 	. 
	rst 38h			;daf1	ff 	. 
	rst 38h			;daf2	ff 	. 
	rst 38h			;daf3	ff 	. 
	rst 38h			;daf4	ff 	. 
	rst 38h			;daf5	ff 	. 
	rst 38h			;daf6	ff 	. 
	rst 38h			;daf7	ff 	. 
	rst 38h			;daf8	ff 	. 
	rst 38h			;daf9	ff 	. 
	rst 38h			;dafa	ff 	. 
	rst 38h			;dafb	ff 	. 
	rst 38h			;dafc	ff 	. 
	rst 38h			;dafd	ff 	. 
	rst 38h			;dafe	ff 	. 
	rst 38h			;daff	ff 	. 
	rst 38h			;db00	ff 	. 
	rst 38h			;db01	ff 	. 
	rst 38h			;db02	ff 	. 
	rst 38h			;db03	ff 	. 
	rst 38h			;db04	ff 	. 
	rst 38h			;db05	ff 	. 
	rst 38h			;db06	ff 	. 
	rst 38h			;db07	ff 	. 
	rst 38h			;db08	ff 	. 
	rst 38h			;db09	ff 	. 
	rst 38h			;db0a	ff 	. 
	rst 38h			;db0b	ff 	. 
	rst 38h			;db0c	ff 	. 
	rst 38h			;db0d	ff 	. 
	rst 38h			;db0e	ff 	. 
	rst 38h			;db0f	ff 	. 
	rst 38h			;db10	ff 	. 
	rst 38h			;db11	ff 	. 
	rst 38h			;db12	ff 	. 
	rst 38h			;db13	ff 	. 
	rst 38h			;db14	ff 	. 
	rst 38h			;db15	ff 	. 
	rst 38h			;db16	ff 	. 
	rst 38h			;db17	ff 	. 
	rst 38h			;db18	ff 	. 
	rst 38h			;db19	ff 	. 
	rst 38h			;db1a	ff 	. 
	rst 38h			;db1b	ff 	. 
	rst 38h			;db1c	ff 	. 
	rst 38h			;db1d	ff 	. 
	rst 38h			;db1e	ff 	. 
	rst 38h			;db1f	ff 	. 
	rst 38h			;db20	ff 	. 
	rst 38h			;db21	ff 	. 
	rst 38h			;db22	ff 	. 
	rst 38h			;db23	ff 	. 
	rst 38h			;db24	ff 	. 
	rst 38h			;db25	ff 	. 
	rst 38h			;db26	ff 	. 
	rst 38h			;db27	ff 	. 
	rst 38h			;db28	ff 	. 
	rst 38h			;db29	ff 	. 
	rst 38h			;db2a	ff 	. 
	rst 38h			;db2b	ff 	. 
	rst 38h			;db2c	ff 	. 
	rst 38h			;db2d	ff 	. 
	rst 38h			;db2e	ff 	. 
	rst 38h			;db2f	ff 	. 
	rst 38h			;db30	ff 	. 
	rst 38h			;db31	ff 	. 
	rst 38h			;db32	ff 	. 
	rst 38h			;db33	ff 	. 
	rst 38h			;db34	ff 	. 
	rst 38h			;db35	ff 	. 
	rst 38h			;db36	ff 	. 
	rst 38h			;db37	ff 	. 
	rst 38h			;db38	ff 	. 
	rst 38h			;db39	ff 	. 
	rst 38h			;db3a	ff 	. 
	rst 38h			;db3b	ff 	. 
	rst 38h			;db3c	ff 	. 
	rst 38h			;db3d	ff 	. 
	rst 38h			;db3e	ff 	. 
	rst 38h			;db3f	ff 	. 
	rst 38h			;db40	ff 	. 
	rst 38h			;db41	ff 	. 
	rst 38h			;db42	ff 	. 
	rst 38h			;db43	ff 	. 
	rst 38h			;db44	ff 	. 
	rst 38h			;db45	ff 	. 
	rst 38h			;db46	ff 	. 
	rst 38h			;db47	ff 	. 
	rst 38h			;db48	ff 	. 
	rst 38h			;db49	ff 	. 
	rst 38h			;db4a	ff 	. 
	rst 38h			;db4b	ff 	. 
	rst 38h			;db4c	ff 	. 
	rst 38h			;db4d	ff 	. 
	rst 38h			;db4e	ff 	. 
	rst 38h			;db4f	ff 	. 
	rst 38h			;db50	ff 	. 
	rst 38h			;db51	ff 	. 
	rst 38h			;db52	ff 	. 
	rst 38h			;db53	ff 	. 
	rst 38h			;db54	ff 	. 
	rst 38h			;db55	ff 	. 
	rst 38h			;db56	ff 	. 
	rst 38h			;db57	ff 	. 
	rst 38h			;db58	ff 	. 
	rst 38h			;db59	ff 	. 
	rst 38h			;db5a	ff 	. 
	rst 38h			;db5b	ff 	. 
	rst 38h			;db5c	ff 	. 
	rst 38h			;db5d	ff 	. 
	rst 38h			;db5e	ff 	. 
	rst 38h			;db5f	ff 	. 
	rst 38h			;db60	ff 	. 
	rst 38h			;db61	ff 	. 
	rst 38h			;db62	ff 	. 
	rst 38h			;db63	ff 	. 
	rst 38h			;db64	ff 	. 
	rst 38h			;db65	ff 	. 
	rst 38h			;db66	ff 	. 
	rst 38h			;db67	ff 	. 
	rst 38h			;db68	ff 	. 
	rst 38h			;db69	ff 	. 
	rst 38h			;db6a	ff 	. 
	rst 38h			;db6b	ff 	. 
	rst 38h			;db6c	ff 	. 
	rst 38h			;db6d	ff 	. 
	rst 38h			;db6e	ff 	. 
	rst 38h			;db6f	ff 	. 
	rst 38h			;db70	ff 	. 
	rst 38h			;db71	ff 	. 
	rst 38h			;db72	ff 	. 
	rst 38h			;db73	ff 	. 
	rst 38h			;db74	ff 	. 
	rst 38h			;db75	ff 	. 
	rst 38h			;db76	ff 	. 
	rst 38h			;db77	ff 	. 
	rst 38h			;db78	ff 	. 
	rst 38h			;db79	ff 	. 
	rst 38h			;db7a	ff 	. 
	rst 38h			;db7b	ff 	. 
	rst 38h			;db7c	ff 	. 
	rst 38h			;db7d	ff 	. 
	rst 38h			;db7e	ff 	. 
	rst 38h			;db7f	ff 	. 
	rst 38h			;db80	ff 	. 
	rst 38h			;db81	ff 	. 
	rst 38h			;db82	ff 	. 
	rst 38h			;db83	ff 	. 
	rst 38h			;db84	ff 	. 
	rst 38h			;db85	ff 	. 
	rst 38h			;db86	ff 	. 
	rst 38h			;db87	ff 	. 
	rst 38h			;db88	ff 	. 
	rst 38h			;db89	ff 	. 
	rst 38h			;db8a	ff 	. 
	rst 38h			;db8b	ff 	. 
	rst 38h			;db8c	ff 	. 
	rst 38h			;db8d	ff 	. 
	rst 38h			;db8e	ff 	. 
	rst 38h			;db8f	ff 	. 
	rst 38h			;db90	ff 	. 
	rst 38h			;db91	ff 	. 
	rst 38h			;db92	ff 	. 
	rst 38h			;db93	ff 	. 
	rst 38h			;db94	ff 	. 
	rst 38h			;db95	ff 	. 
	rst 38h			;db96	ff 	. 
	rst 38h			;db97	ff 	. 
	rst 38h			;db98	ff 	. 
	rst 38h			;db99	ff 	. 
	rst 38h			;db9a	ff 	. 
	rst 38h			;db9b	ff 	. 
	rst 38h			;db9c	ff 	. 
	rst 38h			;db9d	ff 	. 
	rst 38h			;db9e	ff 	. 
	rst 38h			;db9f	ff 	. 
	rst 38h			;dba0	ff 	. 
	rst 38h			;dba1	ff 	. 
	rst 38h			;dba2	ff 	. 
	rst 38h			;dba3	ff 	. 
	rst 38h			;dba4	ff 	. 
	rst 38h			;dba5	ff 	. 
	rst 38h			;dba6	ff 	. 
	rst 38h			;dba7	ff 	. 
	rst 38h			;dba8	ff 	. 
	rst 38h			;dba9	ff 	. 
	rst 38h			;dbaa	ff 	. 
	rst 38h			;dbab	ff 	. 
	rst 38h			;dbac	ff 	. 
	rst 38h			;dbad	ff 	. 
	rst 38h			;dbae	ff 	. 
	rst 38h			;dbaf	ff 	. 
	rst 38h			;dbb0	ff 	. 
	rst 38h			;dbb1	ff 	. 
	rst 38h			;dbb2	ff 	. 
	rst 38h			;dbb3	ff 	. 
	rst 38h			;dbb4	ff 	. 
	rst 38h			;dbb5	ff 	. 
	rst 38h			;dbb6	ff 	. 
	rst 38h			;dbb7	ff 	. 
	rst 38h			;dbb8	ff 	. 
	rst 38h			;dbb9	ff 	. 
	rst 38h			;dbba	ff 	. 
	rst 38h			;dbbb	ff 	. 
	rst 38h			;dbbc	ff 	. 
	rst 38h			;dbbd	ff 	. 
	rst 38h			;dbbe	ff 	. 
	rst 38h			;dbbf	ff 	. 
	rst 38h			;dbc0	ff 	. 
	rst 38h			;dbc1	ff 	. 
	rst 38h			;dbc2	ff 	. 
	rst 38h			;dbc3	ff 	. 
	rst 38h			;dbc4	ff 	. 
	rst 38h			;dbc5	ff 	. 
	rst 38h			;dbc6	ff 	. 
	rst 38h			;dbc7	ff 	. 
	rst 38h			;dbc8	ff 	. 
	rst 38h			;dbc9	ff 	. 
	rst 38h			;dbca	ff 	. 
	rst 38h			;dbcb	ff 	. 
	rst 38h			;dbcc	ff 	. 
	rst 38h			;dbcd	ff 	. 
	rst 38h			;dbce	ff 	. 
	rst 38h			;dbcf	ff 	. 
	rst 38h			;dbd0	ff 	. 
	rst 38h			;dbd1	ff 	. 
	rst 38h			;dbd2	ff 	. 
	rst 38h			;dbd3	ff 	. 
	rst 38h			;dbd4	ff 	. 
	rst 38h			;dbd5	ff 	. 
	rst 38h			;dbd6	ff 	. 
	rst 38h			;dbd7	ff 	. 
	rst 38h			;dbd8	ff 	. 
	rst 38h			;dbd9	ff 	. 
	rst 38h			;dbda	ff 	. 
	rst 38h			;dbdb	ff 	. 
	rst 38h			;dbdc	ff 	. 
	rst 38h			;dbdd	ff 	. 
	rst 38h			;dbde	ff 	. 
	rst 38h			;dbdf	ff 	. 
	rst 38h			;dbe0	ff 	. 
	rst 38h			;dbe1	ff 	. 
	rst 38h			;dbe2	ff 	. 
	rst 38h			;dbe3	ff 	. 
	rst 38h			;dbe4	ff 	. 
	rst 38h			;dbe5	ff 	. 
	rst 38h			;dbe6	ff 	. 
	rst 38h			;dbe7	ff 	. 
	rst 38h			;dbe8	ff 	. 
	rst 38h			;dbe9	ff 	. 
	rst 38h			;dbea	ff 	. 
	rst 38h			;dbeb	ff 	. 
	rst 38h			;dbec	ff 	. 
	rst 38h			;dbed	ff 	. 
	rst 38h			;dbee	ff 	. 
	rst 38h			;dbef	ff 	. 
	rst 38h			;dbf0	ff 	. 
	rst 38h			;dbf1	ff 	. 
	rst 38h			;dbf2	ff 	. 
	rst 38h			;dbf3	ff 	. 
	rst 38h			;dbf4	ff 	. 
	rst 38h			;dbf5	ff 	. 
	rst 38h			;dbf6	ff 	. 
	rst 38h			;dbf7	ff 	. 
	rst 38h			;dbf8	ff 	. 
	rst 38h			;dbf9	ff 	. 
	rst 38h			;dbfa	ff 	. 
	rst 38h			;dbfb	ff 	. 
	rst 38h			;dbfc	ff 	. 
	rst 38h			;dbfd	ff 	. 
	rst 38h			;dbfe	ff 	. 
	rst 38h			;dbff	ff 	. 
	rst 38h			;dc00	ff 	. 
	rst 38h			;dc01	ff 	. 
	rst 38h			;dc02	ff 	. 
	rst 38h			;dc03	ff 	. 
	rst 38h			;dc04	ff 	. 
	rst 38h			;dc05	ff 	. 
	rst 38h			;dc06	ff 	. 
	rst 38h			;dc07	ff 	. 
	rst 38h			;dc08	ff 	. 
	rst 38h			;dc09	ff 	. 
	rst 38h			;dc0a	ff 	. 
	rst 38h			;dc0b	ff 	. 
	rst 38h			;dc0c	ff 	. 
	rst 38h			;dc0d	ff 	. 
	rst 38h			;dc0e	ff 	. 
	rst 38h			;dc0f	ff 	. 
	rst 38h			;dc10	ff 	. 
	rst 38h			;dc11	ff 	. 
	rst 38h			;dc12	ff 	. 
	rst 38h			;dc13	ff 	. 
	rst 38h			;dc14	ff 	. 
	rst 38h			;dc15	ff 	. 
	rst 38h			;dc16	ff 	. 
	rst 38h			;dc17	ff 	. 
	rst 38h			;dc18	ff 	. 
	rst 38h			;dc19	ff 	. 
	rst 38h			;dc1a	ff 	. 
	rst 38h			;dc1b	ff 	. 
	rst 38h			;dc1c	ff 	. 
	rst 38h			;dc1d	ff 	. 
	rst 38h			;dc1e	ff 	. 
	rst 38h			;dc1f	ff 	. 
	rst 38h			;dc20	ff 	. 
	rst 38h			;dc21	ff 	. 
	rst 38h			;dc22	ff 	. 
	rst 38h			;dc23	ff 	. 
	rst 38h			;dc24	ff 	. 
	rst 38h			;dc25	ff 	. 
	rst 38h			;dc26	ff 	. 
	rst 38h			;dc27	ff 	. 
	rst 38h			;dc28	ff 	. 
	rst 38h			;dc29	ff 	. 
	rst 38h			;dc2a	ff 	. 
	rst 38h			;dc2b	ff 	. 
	rst 38h			;dc2c	ff 	. 
	rst 38h			;dc2d	ff 	. 
	rst 38h			;dc2e	ff 	. 
	rst 38h			;dc2f	ff 	. 
	rst 38h			;dc30	ff 	. 
	rst 38h			;dc31	ff 	. 
	rst 38h			;dc32	ff 	. 
	rst 38h			;dc33	ff 	. 
	rst 38h			;dc34	ff 	. 
	rst 38h			;dc35	ff 	. 
	rst 38h			;dc36	ff 	. 
	rst 38h			;dc37	ff 	. 
	rst 38h			;dc38	ff 	. 
	rst 38h			;dc39	ff 	. 
	rst 38h			;dc3a	ff 	. 
	rst 38h			;dc3b	ff 	. 
	rst 38h			;dc3c	ff 	. 
	rst 38h			;dc3d	ff 	. 
	rst 38h			;dc3e	ff 	. 
	rst 38h			;dc3f	ff 	. 
	rst 38h			;dc40	ff 	. 
	rst 38h			;dc41	ff 	. 
	rst 38h			;dc42	ff 	. 
	rst 38h			;dc43	ff 	. 
	rst 38h			;dc44	ff 	. 
	rst 38h			;dc45	ff 	. 
	rst 38h			;dc46	ff 	. 
	rst 38h			;dc47	ff 	. 
	rst 38h			;dc48	ff 	. 
	rst 38h			;dc49	ff 	. 
	rst 38h			;dc4a	ff 	. 
	rst 38h			;dc4b	ff 	. 
	rst 38h			;dc4c	ff 	. 
	rst 38h			;dc4d	ff 	. 
	rst 38h			;dc4e	ff 	. 
	rst 38h			;dc4f	ff 	. 
	rst 38h			;dc50	ff 	. 
	rst 38h			;dc51	ff 	. 
	rst 38h			;dc52	ff 	. 
	rst 38h			;dc53	ff 	. 
	rst 38h			;dc54	ff 	. 
	rst 38h			;dc55	ff 	. 
	rst 38h			;dc56	ff 	. 
	rst 38h			;dc57	ff 	. 
	rst 38h			;dc58	ff 	. 
	rst 38h			;dc59	ff 	. 
	rst 38h			;dc5a	ff 	. 
	rst 38h			;dc5b	ff 	. 
	rst 38h			;dc5c	ff 	. 
	rst 38h			;dc5d	ff 	. 
	rst 38h			;dc5e	ff 	. 
	rst 38h			;dc5f	ff 	. 
	rst 38h			;dc60	ff 	. 
	rst 38h			;dc61	ff 	. 
	rst 38h			;dc62	ff 	. 
	rst 38h			;dc63	ff 	. 
	rst 38h			;dc64	ff 	. 
	rst 38h			;dc65	ff 	. 
	rst 38h			;dc66	ff 	. 
	rst 38h			;dc67	ff 	. 
	rst 38h			;dc68	ff 	. 
	rst 38h			;dc69	ff 	. 
	rst 38h			;dc6a	ff 	. 
	rst 38h			;dc6b	ff 	. 
	rst 38h			;dc6c	ff 	. 
	rst 38h			;dc6d	ff 	. 
	rst 38h			;dc6e	ff 	. 
	rst 38h			;dc6f	ff 	. 
	rst 38h			;dc70	ff 	. 
	rst 38h			;dc71	ff 	. 
	rst 38h			;dc72	ff 	. 
	rst 38h			;dc73	ff 	. 
	rst 38h			;dc74	ff 	. 
	rst 38h			;dc75	ff 	. 
	rst 38h			;dc76	ff 	. 
	rst 38h			;dc77	ff 	. 
	rst 38h			;dc78	ff 	. 
	rst 38h			;dc79	ff 	. 
	rst 38h			;dc7a	ff 	. 
	rst 38h			;dc7b	ff 	. 
	rst 38h			;dc7c	ff 	. 
	rst 38h			;dc7d	ff 	. 
	rst 38h			;dc7e	ff 	. 
	rst 38h			;dc7f	ff 	. 
	rst 38h			;dc80	ff 	. 
	rst 38h			;dc81	ff 	. 
	rst 38h			;dc82	ff 	. 
	rst 38h			;dc83	ff 	. 
	rst 38h			;dc84	ff 	. 
	rst 38h			;dc85	ff 	. 
	rst 38h			;dc86	ff 	. 
	rst 38h			;dc87	ff 	. 
	rst 38h			;dc88	ff 	. 
	rst 38h			;dc89	ff 	. 
	rst 38h			;dc8a	ff 	. 
	rst 38h			;dc8b	ff 	. 
	rst 38h			;dc8c	ff 	. 
	rst 38h			;dc8d	ff 	. 
	rst 38h			;dc8e	ff 	. 
	rst 38h			;dc8f	ff 	. 
	rst 38h			;dc90	ff 	. 
	rst 38h			;dc91	ff 	. 
	rst 38h			;dc92	ff 	. 
	rst 38h			;dc93	ff 	. 
	rst 38h			;dc94	ff 	. 
	rst 38h			;dc95	ff 	. 
	rst 38h			;dc96	ff 	. 
	rst 38h			;dc97	ff 	. 
	rst 38h			;dc98	ff 	. 
	rst 38h			;dc99	ff 	. 
	rst 38h			;dc9a	ff 	. 
	rst 38h			;dc9b	ff 	. 
	rst 38h			;dc9c	ff 	. 
	rst 38h			;dc9d	ff 	. 
	rst 38h			;dc9e	ff 	. 
	rst 38h			;dc9f	ff 	. 
	rst 38h			;dca0	ff 	. 
	rst 38h			;dca1	ff 	. 
	rst 38h			;dca2	ff 	. 
	rst 38h			;dca3	ff 	. 
	rst 38h			;dca4	ff 	. 
	rst 38h			;dca5	ff 	. 
	rst 38h			;dca6	ff 	. 
	rst 38h			;dca7	ff 	. 
	rst 38h			;dca8	ff 	. 
	rst 38h			;dca9	ff 	. 
	rst 38h			;dcaa	ff 	. 
	rst 38h			;dcab	ff 	. 
	rst 38h			;dcac	ff 	. 
	rst 38h			;dcad	ff 	. 
	rst 38h			;dcae	ff 	. 
	rst 38h			;dcaf	ff 	. 
	rst 38h			;dcb0	ff 	. 
	rst 38h			;dcb1	ff 	. 
	rst 38h			;dcb2	ff 	. 
	rst 38h			;dcb3	ff 	. 
	rst 38h			;dcb4	ff 	. 
	rst 38h			;dcb5	ff 	. 
	rst 38h			;dcb6	ff 	. 
	rst 38h			;dcb7	ff 	. 
	rst 38h			;dcb8	ff 	. 
	rst 38h			;dcb9	ff 	. 
	rst 38h			;dcba	ff 	. 
	rst 38h			;dcbb	ff 	. 
	rst 38h			;dcbc	ff 	. 
	rst 38h			;dcbd	ff 	. 
	rst 38h			;dcbe	ff 	. 
	rst 38h			;dcbf	ff 	. 
	rst 38h			;dcc0	ff 	. 
	rst 38h			;dcc1	ff 	. 
	rst 38h			;dcc2	ff 	. 
	rst 38h			;dcc3	ff 	. 
	rst 38h			;dcc4	ff 	. 
	rst 38h			;dcc5	ff 	. 
	rst 38h			;dcc6	ff 	. 
	rst 38h			;dcc7	ff 	. 
	rst 38h			;dcc8	ff 	. 
	rst 38h			;dcc9	ff 	. 
	rst 38h			;dcca	ff 	. 
	rst 38h			;dccb	ff 	. 
	rst 38h			;dccc	ff 	. 
	rst 38h			;dccd	ff 	. 
	rst 38h			;dcce	ff 	. 
	rst 38h			;dccf	ff 	. 
	rst 38h			;dcd0	ff 	. 
	rst 38h			;dcd1	ff 	. 
	rst 38h			;dcd2	ff 	. 
	rst 38h			;dcd3	ff 	. 
	rst 38h			;dcd4	ff 	. 
	rst 38h			;dcd5	ff 	. 
	rst 38h			;dcd6	ff 	. 
	rst 38h			;dcd7	ff 	. 
	rst 38h			;dcd8	ff 	. 
	rst 38h			;dcd9	ff 	. 
	rst 38h			;dcda	ff 	. 
	rst 38h			;dcdb	ff 	. 
	rst 38h			;dcdc	ff 	. 
	rst 38h			;dcdd	ff 	. 
	rst 38h			;dcde	ff 	. 
	rst 38h			;dcdf	ff 	. 
	rst 38h			;dce0	ff 	. 
	rst 38h			;dce1	ff 	. 
	rst 38h			;dce2	ff 	. 
	rst 38h			;dce3	ff 	. 
	rst 38h			;dce4	ff 	. 
	rst 38h			;dce5	ff 	. 
	rst 38h			;dce6	ff 	. 
	rst 38h			;dce7	ff 	. 
	rst 38h			;dce8	ff 	. 
	rst 38h			;dce9	ff 	. 
	rst 38h			;dcea	ff 	. 
	rst 38h			;dceb	ff 	. 
	rst 38h			;dcec	ff 	. 
	rst 38h			;dced	ff 	. 
	rst 38h			;dcee	ff 	. 
	rst 38h			;dcef	ff 	. 
	rst 38h			;dcf0	ff 	. 
	rst 38h			;dcf1	ff 	. 
	rst 38h			;dcf2	ff 	. 
	rst 38h			;dcf3	ff 	. 
	rst 38h			;dcf4	ff 	. 
	rst 38h			;dcf5	ff 	. 
	rst 38h			;dcf6	ff 	. 
	rst 38h			;dcf7	ff 	. 
	rst 38h			;dcf8	ff 	. 
	rst 38h			;dcf9	ff 	. 
	rst 38h			;dcfa	ff 	. 
	rst 38h			;dcfb	ff 	. 
	rst 38h			;dcfc	ff 	. 
	rst 38h			;dcfd	ff 	. 
	rst 38h			;dcfe	ff 	. 
	rst 38h			;dcff	ff 	. 
	rst 38h			;dd00	ff 	. 
	rst 38h			;dd01	ff 	. 
	rst 38h			;dd02	ff 	. 
	rst 38h			;dd03	ff 	. 
	rst 38h			;dd04	ff 	. 
	rst 38h			;dd05	ff 	. 
	rst 38h			;dd06	ff 	. 
	rst 38h			;dd07	ff 	. 
	rst 38h			;dd08	ff 	. 
	rst 38h			;dd09	ff 	. 
	rst 38h			;dd0a	ff 	. 
	rst 38h			;dd0b	ff 	. 
	rst 38h			;dd0c	ff 	. 
	rst 38h			;dd0d	ff 	. 
	rst 38h			;dd0e	ff 	. 
	rst 38h			;dd0f	ff 	. 
	rst 38h			;dd10	ff 	. 
	rst 38h			;dd11	ff 	. 
	rst 38h			;dd12	ff 	. 
	rst 38h			;dd13	ff 	. 
	rst 38h			;dd14	ff 	. 
	rst 38h			;dd15	ff 	. 
	rst 38h			;dd16	ff 	. 
	rst 38h			;dd17	ff 	. 
	rst 38h			;dd18	ff 	. 
	rst 38h			;dd19	ff 	. 
	rst 38h			;dd1a	ff 	. 
	rst 38h			;dd1b	ff 	. 
	rst 38h			;dd1c	ff 	. 
	rst 38h			;dd1d	ff 	. 
	rst 38h			;dd1e	ff 	. 
	rst 38h			;dd1f	ff 	. 
	rst 38h			;dd20	ff 	. 
	rst 38h			;dd21	ff 	. 
	rst 38h			;dd22	ff 	. 
	rst 38h			;dd23	ff 	. 
	rst 38h			;dd24	ff 	. 
	rst 38h			;dd25	ff 	. 
	rst 38h			;dd26	ff 	. 
	rst 38h			;dd27	ff 	. 
	rst 38h			;dd28	ff 	. 
	rst 38h			;dd29	ff 	. 
	rst 38h			;dd2a	ff 	. 
	rst 38h			;dd2b	ff 	. 
	rst 38h			;dd2c	ff 	. 
	rst 38h			;dd2d	ff 	. 
	rst 38h			;dd2e	ff 	. 
	rst 38h			;dd2f	ff 	. 
	rst 38h			;dd30	ff 	. 
	rst 38h			;dd31	ff 	. 
	rst 38h			;dd32	ff 	. 
	rst 38h			;dd33	ff 	. 
	rst 38h			;dd34	ff 	. 
	rst 38h			;dd35	ff 	. 
	rst 38h			;dd36	ff 	. 
	rst 38h			;dd37	ff 	. 
	rst 38h			;dd38	ff 	. 
	rst 38h			;dd39	ff 	. 
	rst 38h			;dd3a	ff 	. 
	rst 38h			;dd3b	ff 	. 
	rst 38h			;dd3c	ff 	. 
	rst 38h			;dd3d	ff 	. 
	rst 38h			;dd3e	ff 	. 
	rst 38h			;dd3f	ff 	. 
	rst 38h			;dd40	ff 	. 
	rst 38h			;dd41	ff 	. 
	rst 38h			;dd42	ff 	. 
	rst 38h			;dd43	ff 	. 
	rst 38h			;dd44	ff 	. 
	rst 38h			;dd45	ff 	. 
	rst 38h			;dd46	ff 	. 
	rst 38h			;dd47	ff 	. 
	rst 38h			;dd48	ff 	. 
	rst 38h			;dd49	ff 	. 
	rst 38h			;dd4a	ff 	. 
	rst 38h			;dd4b	ff 	. 
	rst 38h			;dd4c	ff 	. 
	rst 38h			;dd4d	ff 	. 
	rst 38h			;dd4e	ff 	. 
	rst 38h			;dd4f	ff 	. 
	rst 38h			;dd50	ff 	. 
	rst 38h			;dd51	ff 	. 
	rst 38h			;dd52	ff 	. 
	rst 38h			;dd53	ff 	. 
	rst 38h			;dd54	ff 	. 
	rst 38h			;dd55	ff 	. 
	rst 38h			;dd56	ff 	. 
	rst 38h			;dd57	ff 	. 
	rst 38h			;dd58	ff 	. 
	rst 38h			;dd59	ff 	. 
	rst 38h			;dd5a	ff 	. 
	rst 38h			;dd5b	ff 	. 
	rst 38h			;dd5c	ff 	. 
	rst 38h			;dd5d	ff 	. 
	rst 38h			;dd5e	ff 	. 
	rst 38h			;dd5f	ff 	. 
	rst 38h			;dd60	ff 	. 
	rst 38h			;dd61	ff 	. 
	rst 38h			;dd62	ff 	. 
	rst 38h			;dd63	ff 	. 
	rst 38h			;dd64	ff 	. 
	rst 38h			;dd65	ff 	. 
	rst 38h			;dd66	ff 	. 
	rst 38h			;dd67	ff 	. 
	rst 38h			;dd68	ff 	. 
	rst 38h			;dd69	ff 	. 
	rst 38h			;dd6a	ff 	. 
	rst 38h			;dd6b	ff 	. 
	rst 38h			;dd6c	ff 	. 
	rst 38h			;dd6d	ff 	. 
	rst 38h			;dd6e	ff 	. 
	rst 38h			;dd6f	ff 	. 
	rst 38h			;dd70	ff 	. 
	rst 38h			;dd71	ff 	. 
	rst 38h			;dd72	ff 	. 
	rst 38h			;dd73	ff 	. 
	rst 38h			;dd74	ff 	. 
	rst 38h			;dd75	ff 	. 
	rst 38h			;dd76	ff 	. 
	rst 38h			;dd77	ff 	. 
	rst 38h			;dd78	ff 	. 
	rst 38h			;dd79	ff 	. 
	rst 38h			;dd7a	ff 	. 
	rst 38h			;dd7b	ff 	. 
	rst 38h			;dd7c	ff 	. 
	rst 38h			;dd7d	ff 	. 
	rst 38h			;dd7e	ff 	. 
	rst 38h			;dd7f	ff 	. 
	rst 38h			;dd80	ff 	. 
	rst 38h			;dd81	ff 	. 
	rst 38h			;dd82	ff 	. 
	rst 38h			;dd83	ff 	. 
	rst 38h			;dd84	ff 	. 
	rst 38h			;dd85	ff 	. 
	rst 38h			;dd86	ff 	. 
	rst 38h			;dd87	ff 	. 
	rst 38h			;dd88	ff 	. 
	rst 38h			;dd89	ff 	. 
	rst 38h			;dd8a	ff 	. 
	rst 38h			;dd8b	ff 	. 
	rst 38h			;dd8c	ff 	. 
	rst 38h			;dd8d	ff 	. 
	rst 38h			;dd8e	ff 	. 
	rst 38h			;dd8f	ff 	. 
	rst 38h			;dd90	ff 	. 
	rst 38h			;dd91	ff 	. 
	rst 38h			;dd92	ff 	. 
	rst 38h			;dd93	ff 	. 
	rst 38h			;dd94	ff 	. 
	rst 38h			;dd95	ff 	. 
	rst 38h			;dd96	ff 	. 
	rst 38h			;dd97	ff 	. 
	rst 38h			;dd98	ff 	. 
	rst 38h			;dd99	ff 	. 
	rst 38h			;dd9a	ff 	. 
	rst 38h			;dd9b	ff 	. 
	rst 38h			;dd9c	ff 	. 
	rst 38h			;dd9d	ff 	. 
	rst 38h			;dd9e	ff 	. 
	rst 38h			;dd9f	ff 	. 
	rst 38h			;dda0	ff 	. 
	rst 38h			;dda1	ff 	. 
	rst 38h			;dda2	ff 	. 
	rst 38h			;dda3	ff 	. 
	rst 38h			;dda4	ff 	. 
	rst 38h			;dda5	ff 	. 
	rst 38h			;dda6	ff 	. 
	rst 38h			;dda7	ff 	. 
	rst 38h			;dda8	ff 	. 
	rst 38h			;dda9	ff 	. 
	rst 38h			;ddaa	ff 	. 
	rst 38h			;ddab	ff 	. 
	rst 38h			;ddac	ff 	. 
	rst 38h			;ddad	ff 	. 
	rst 38h			;ddae	ff 	. 
	rst 38h			;ddaf	ff 	. 
	rst 38h			;ddb0	ff 	. 
	rst 38h			;ddb1	ff 	. 
	rst 38h			;ddb2	ff 	. 
	rst 38h			;ddb3	ff 	. 
	rst 38h			;ddb4	ff 	. 
	rst 38h			;ddb5	ff 	. 
	rst 38h			;ddb6	ff 	. 
	rst 38h			;ddb7	ff 	. 
	rst 38h			;ddb8	ff 	. 
	rst 38h			;ddb9	ff 	. 
	rst 38h			;ddba	ff 	. 
	rst 38h			;ddbb	ff 	. 
	rst 38h			;ddbc	ff 	. 
	rst 38h			;ddbd	ff 	. 
	rst 38h			;ddbe	ff 	. 
	rst 38h			;ddbf	ff 	. 
	rst 38h			;ddc0	ff 	. 
	rst 38h			;ddc1	ff 	. 
	rst 38h			;ddc2	ff 	. 
	rst 38h			;ddc3	ff 	. 
	rst 38h			;ddc4	ff 	. 
	rst 38h			;ddc5	ff 	. 
	rst 38h			;ddc6	ff 	. 
	rst 38h			;ddc7	ff 	. 
	rst 38h			;ddc8	ff 	. 
	rst 38h			;ddc9	ff 	. 
	rst 38h			;ddca	ff 	. 
	rst 38h			;ddcb	ff 	. 
	rst 38h			;ddcc	ff 	. 
	rst 38h			;ddcd	ff 	. 
	rst 38h			;ddce	ff 	. 
	rst 38h			;ddcf	ff 	. 
	rst 38h			;ddd0	ff 	. 
	rst 38h			;ddd1	ff 	. 
	rst 38h			;ddd2	ff 	. 
	rst 38h			;ddd3	ff 	. 
	rst 38h			;ddd4	ff 	. 
	rst 38h			;ddd5	ff 	. 
	rst 38h			;ddd6	ff 	. 
	rst 38h			;ddd7	ff 	. 
	rst 38h			;ddd8	ff 	. 
	rst 38h			;ddd9	ff 	. 
	rst 38h			;ddda	ff 	. 
	rst 38h			;dddb	ff 	. 
	rst 38h			;dddc	ff 	. 
	rst 38h			;dddd	ff 	. 
	rst 38h			;ddde	ff 	. 
	rst 38h			;dddf	ff 	. 
	rst 38h			;dde0	ff 	. 
	rst 38h			;dde1	ff 	. 
	rst 38h			;dde2	ff 	. 
	rst 38h			;dde3	ff 	. 
	rst 38h			;dde4	ff 	. 
	rst 38h			;dde5	ff 	. 
	rst 38h			;dde6	ff 	. 
	rst 38h			;dde7	ff 	. 
	rst 38h			;dde8	ff 	. 
	rst 38h			;dde9	ff 	. 
	rst 38h			;ddea	ff 	. 
	rst 38h			;ddeb	ff 	. 
	rst 38h			;ddec	ff 	. 
	rst 38h			;dded	ff 	. 
	rst 38h			;ddee	ff 	. 
	rst 38h			;ddef	ff 	. 
	rst 38h			;ddf0	ff 	. 
	rst 38h			;ddf1	ff 	. 
	rst 38h			;ddf2	ff 	. 
	rst 38h			;ddf3	ff 	. 
	rst 38h			;ddf4	ff 	. 
	rst 38h			;ddf5	ff 	. 
	rst 38h			;ddf6	ff 	. 
	rst 38h			;ddf7	ff 	. 
	rst 38h			;ddf8	ff 	. 
	rst 38h			;ddf9	ff 	. 
	rst 38h			;ddfa	ff 	. 
	rst 38h			;ddfb	ff 	. 
	rst 38h			;ddfc	ff 	. 
	rst 38h			;ddfd	ff 	. 
	rst 38h			;ddfe	ff 	. 
	rst 38h			;ddff	ff 	. 
	rst 38h			;de00	ff 	. 
	rst 38h			;de01	ff 	. 
	rst 38h			;de02	ff 	. 
	rst 38h			;de03	ff 	. 
	rst 38h			;de04	ff 	. 
	rst 38h			;de05	ff 	. 
	rst 38h			;de06	ff 	. 
	rst 38h			;de07	ff 	. 
	rst 38h			;de08	ff 	. 
	rst 38h			;de09	ff 	. 
	rst 38h			;de0a	ff 	. 
	rst 38h			;de0b	ff 	. 
	rst 38h			;de0c	ff 	. 
	rst 38h			;de0d	ff 	. 
	rst 38h			;de0e	ff 	. 
	rst 38h			;de0f	ff 	. 
	rst 38h			;de10	ff 	. 
	rst 38h			;de11	ff 	. 
	rst 38h			;de12	ff 	. 
	rst 38h			;de13	ff 	. 
	rst 38h			;de14	ff 	. 
	rst 38h			;de15	ff 	. 
	rst 38h			;de16	ff 	. 
	rst 38h			;de17	ff 	. 
	rst 38h			;de18	ff 	. 
	rst 38h			;de19	ff 	. 
	rst 38h			;de1a	ff 	. 
	rst 38h			;de1b	ff 	. 
	rst 38h			;de1c	ff 	. 
	rst 38h			;de1d	ff 	. 
	rst 38h			;de1e	ff 	. 
	rst 38h			;de1f	ff 	. 
	rst 38h			;de20	ff 	. 
	rst 38h			;de21	ff 	. 
	rst 38h			;de22	ff 	. 
	rst 38h			;de23	ff 	. 
	rst 38h			;de24	ff 	. 
	rst 38h			;de25	ff 	. 
	rst 38h			;de26	ff 	. 
	rst 38h			;de27	ff 	. 
	rst 38h			;de28	ff 	. 
	rst 38h			;de29	ff 	. 
	rst 38h			;de2a	ff 	. 
	rst 38h			;de2b	ff 	. 
	rst 38h			;de2c	ff 	. 
	rst 38h			;de2d	ff 	. 
	rst 38h			;de2e	ff 	. 
	rst 38h			;de2f	ff 	. 
	rst 38h			;de30	ff 	. 
	rst 38h			;de31	ff 	. 
	rst 38h			;de32	ff 	. 
	rst 38h			;de33	ff 	. 
	rst 38h			;de34	ff 	. 
	rst 38h			;de35	ff 	. 
	rst 38h			;de36	ff 	. 
	rst 38h			;de37	ff 	. 
	rst 38h			;de38	ff 	. 
	rst 38h			;de39	ff 	. 
	rst 38h			;de3a	ff 	. 
	rst 38h			;de3b	ff 	. 
	rst 38h			;de3c	ff 	. 
	rst 38h			;de3d	ff 	. 
	rst 38h			;de3e	ff 	. 
	rst 38h			;de3f	ff 	. 
	rst 38h			;de40	ff 	. 
	rst 38h			;de41	ff 	. 
	rst 38h			;de42	ff 	. 
	rst 38h			;de43	ff 	. 
	rst 38h			;de44	ff 	. 
	rst 38h			;de45	ff 	. 
	rst 38h			;de46	ff 	. 
	rst 38h			;de47	ff 	. 
	rst 38h			;de48	ff 	. 
	rst 38h			;de49	ff 	. 
	rst 38h			;de4a	ff 	. 
	rst 38h			;de4b	ff 	. 
	rst 38h			;de4c	ff 	. 
	rst 38h			;de4d	ff 	. 
	rst 38h			;de4e	ff 	. 
	rst 38h			;de4f	ff 	. 
	rst 38h			;de50	ff 	. 
	rst 38h			;de51	ff 	. 
	rst 38h			;de52	ff 	. 
	rst 38h			;de53	ff 	. 
	rst 38h			;de54	ff 	. 
	rst 38h			;de55	ff 	. 
	rst 38h			;de56	ff 	. 
	rst 38h			;de57	ff 	. 
	rst 38h			;de58	ff 	. 
	rst 38h			;de59	ff 	. 
	rst 38h			;de5a	ff 	. 
	rst 38h			;de5b	ff 	. 
	rst 38h			;de5c	ff 	. 
	rst 38h			;de5d	ff 	. 
	rst 38h			;de5e	ff 	. 
	rst 38h			;de5f	ff 	. 
	rst 38h			;de60	ff 	. 
	rst 38h			;de61	ff 	. 
	rst 38h			;de62	ff 	. 
	rst 38h			;de63	ff 	. 
	rst 38h			;de64	ff 	. 
	rst 38h			;de65	ff 	. 
	rst 38h			;de66	ff 	. 
	rst 38h			;de67	ff 	. 
	rst 38h			;de68	ff 	. 
	rst 38h			;de69	ff 	. 
	rst 38h			;de6a	ff 	. 
	rst 38h			;de6b	ff 	. 
	rst 38h			;de6c	ff 	. 
	rst 38h			;de6d	ff 	. 
	rst 38h			;de6e	ff 	. 
	rst 38h			;de6f	ff 	. 
	rst 38h			;de70	ff 	. 
	rst 38h			;de71	ff 	. 
	rst 38h			;de72	ff 	. 
	rst 38h			;de73	ff 	. 
	rst 38h			;de74	ff 	. 
	rst 38h			;de75	ff 	. 
	rst 38h			;de76	ff 	. 
	rst 38h			;de77	ff 	. 
	rst 38h			;de78	ff 	. 
	rst 38h			;de79	ff 	. 
	rst 38h			;de7a	ff 	. 
	rst 38h			;de7b	ff 	. 
	rst 38h			;de7c	ff 	. 
	rst 38h			;de7d	ff 	. 
	rst 38h			;de7e	ff 	. 
	rst 38h			;de7f	ff 	. 
	rst 38h			;de80	ff 	. 
	rst 38h			;de81	ff 	. 
	rst 38h			;de82	ff 	. 
	rst 38h			;de83	ff 	. 
	rst 38h			;de84	ff 	. 
	rst 38h			;de85	ff 	. 
	rst 38h			;de86	ff 	. 
	rst 38h			;de87	ff 	. 
	rst 38h			;de88	ff 	. 
	rst 38h			;de89	ff 	. 
	rst 38h			;de8a	ff 	. 
	rst 38h			;de8b	ff 	. 
	rst 38h			;de8c	ff 	. 
	rst 38h			;de8d	ff 	. 
	rst 38h			;de8e	ff 	. 
	rst 38h			;de8f	ff 	. 
	rst 38h			;de90	ff 	. 
	rst 38h			;de91	ff 	. 
	rst 38h			;de92	ff 	. 
	rst 38h			;de93	ff 	. 
	rst 38h			;de94	ff 	. 
	rst 38h			;de95	ff 	. 
	rst 38h			;de96	ff 	. 
	rst 38h			;de97	ff 	. 
	rst 38h			;de98	ff 	. 
	rst 38h			;de99	ff 	. 
	rst 38h			;de9a	ff 	. 
	rst 38h			;de9b	ff 	. 
	rst 38h			;de9c	ff 	. 
	rst 38h			;de9d	ff 	. 
	rst 38h			;de9e	ff 	. 
	rst 38h			;de9f	ff 	. 
	rst 38h			;dea0	ff 	. 
	rst 38h			;dea1	ff 	. 
	rst 38h			;dea2	ff 	. 
	rst 38h			;dea3	ff 	. 
	rst 38h			;dea4	ff 	. 
	rst 38h			;dea5	ff 	. 
	rst 38h			;dea6	ff 	. 
	rst 38h			;dea7	ff 	. 
	rst 38h			;dea8	ff 	. 
	rst 38h			;dea9	ff 	. 
	rst 38h			;deaa	ff 	. 
	rst 38h			;deab	ff 	. 
	rst 38h			;deac	ff 	. 
	rst 38h			;dead	ff 	. 
	rst 38h			;deae	ff 	. 
	rst 38h			;deaf	ff 	. 
	rst 38h			;deb0	ff 	. 
	rst 38h			;deb1	ff 	. 
	rst 38h			;deb2	ff 	. 
	rst 38h			;deb3	ff 	. 
	rst 38h			;deb4	ff 	. 
	rst 38h			;deb5	ff 	. 
	rst 38h			;deb6	ff 	. 
	rst 38h			;deb7	ff 	. 
	rst 38h			;deb8	ff 	. 
	rst 38h			;deb9	ff 	. 
	rst 38h			;deba	ff 	. 
	rst 38h			;debb	ff 	. 
	rst 38h			;debc	ff 	. 
	rst 38h			;debd	ff 	. 
	rst 38h			;debe	ff 	. 
	rst 38h			;debf	ff 	. 
	rst 38h			;dec0	ff 	. 
	rst 38h			;dec1	ff 	. 
	rst 38h			;dec2	ff 	. 
	rst 38h			;dec3	ff 	. 
	rst 38h			;dec4	ff 	. 
	rst 38h			;dec5	ff 	. 
	rst 38h			;dec6	ff 	. 
	rst 38h			;dec7	ff 	. 
	rst 38h			;dec8	ff 	. 
	rst 38h			;dec9	ff 	. 
	rst 38h			;deca	ff 	. 
	rst 38h			;decb	ff 	. 
	rst 38h			;decc	ff 	. 
	rst 38h			;decd	ff 	. 
	rst 38h			;dece	ff 	. 
	rst 38h			;decf	ff 	. 
	rst 38h			;ded0	ff 	. 
	rst 38h			;ded1	ff 	. 
	rst 38h			;ded2	ff 	. 
	rst 38h			;ded3	ff 	. 
	rst 38h			;ded4	ff 	. 
	rst 38h			;ded5	ff 	. 
	rst 38h			;ded6	ff 	. 
	rst 38h			;ded7	ff 	. 
	rst 38h			;ded8	ff 	. 
	rst 38h			;ded9	ff 	. 
	rst 38h			;deda	ff 	. 
	rst 38h			;dedb	ff 	. 
	rst 38h			;dedc	ff 	. 
	rst 38h			;dedd	ff 	. 
	rst 38h			;dede	ff 	. 
	rst 38h			;dedf	ff 	. 
	rst 38h			;dee0	ff 	. 
	rst 38h			;dee1	ff 	. 
	rst 38h			;dee2	ff 	. 
	rst 38h			;dee3	ff 	. 
	rst 38h			;dee4	ff 	. 
	rst 38h			;dee5	ff 	. 
	rst 38h			;dee6	ff 	. 
	rst 38h			;dee7	ff 	. 
	rst 38h			;dee8	ff 	. 
	rst 38h			;dee9	ff 	. 
	rst 38h			;deea	ff 	. 
	rst 38h			;deeb	ff 	. 
	rst 38h			;deec	ff 	. 
	rst 38h			;deed	ff 	. 
	rst 38h			;deee	ff 	. 
	rst 38h			;deef	ff 	. 
	rst 38h			;def0	ff 	. 
	rst 38h			;def1	ff 	. 
	rst 38h			;def2	ff 	. 
	rst 38h			;def3	ff 	. 
	rst 38h			;def4	ff 	. 
	rst 38h			;def5	ff 	. 
	rst 38h			;def6	ff 	. 
	rst 38h			;def7	ff 	. 
	rst 38h			;def8	ff 	. 
	rst 38h			;def9	ff 	. 
	rst 38h			;defa	ff 	. 
	rst 38h			;defb	ff 	. 
	rst 38h			;defc	ff 	. 
	rst 38h			;defd	ff 	. 
	rst 38h			;defe	ff 	. 
	rst 38h			;deff	ff 	. 
	rst 38h			;df00	ff 	. 
	rst 38h			;df01	ff 	. 
	rst 38h			;df02	ff 	. 
	rst 38h			;df03	ff 	. 
	rst 38h			;df04	ff 	. 
	rst 38h			;df05	ff 	. 
	rst 38h			;df06	ff 	. 
	rst 38h			;df07	ff 	. 
	rst 38h			;df08	ff 	. 
	rst 38h			;df09	ff 	. 
	rst 38h			;df0a	ff 	. 
	rst 38h			;df0b	ff 	. 
	rst 38h			;df0c	ff 	. 
	rst 38h			;df0d	ff 	. 
	rst 38h			;df0e	ff 	. 
	rst 38h			;df0f	ff 	. 
	rst 38h			;df10	ff 	. 
	rst 38h			;df11	ff 	. 
	rst 38h			;df12	ff 	. 
	rst 38h			;df13	ff 	. 
	rst 38h			;df14	ff 	. 
	rst 38h			;df15	ff 	. 
	rst 38h			;df16	ff 	. 
	rst 38h			;df17	ff 	. 
	rst 38h			;df18	ff 	. 
	rst 38h			;df19	ff 	. 
	rst 38h			;df1a	ff 	. 
	rst 38h			;df1b	ff 	. 
	rst 38h			;df1c	ff 	. 
	rst 38h			;df1d	ff 	. 
	rst 38h			;df1e	ff 	. 
	rst 38h			;df1f	ff 	. 
	rst 38h			;df20	ff 	. 
	rst 38h			;df21	ff 	. 
	rst 38h			;df22	ff 	. 
	rst 38h			;df23	ff 	. 
	rst 38h			;df24	ff 	. 
	rst 38h			;df25	ff 	. 
	rst 38h			;df26	ff 	. 
	rst 38h			;df27	ff 	. 
	rst 38h			;df28	ff 	. 
	rst 38h			;df29	ff 	. 
	rst 38h			;df2a	ff 	. 
	rst 38h			;df2b	ff 	. 
	rst 38h			;df2c	ff 	. 
	rst 38h			;df2d	ff 	. 
	rst 38h			;df2e	ff 	. 
	rst 38h			;df2f	ff 	. 
	rst 38h			;df30	ff 	. 
	rst 38h			;df31	ff 	. 
	rst 38h			;df32	ff 	. 
	rst 38h			;df33	ff 	. 
	rst 38h			;df34	ff 	. 
	rst 38h			;df35	ff 	. 
	rst 38h			;df36	ff 	. 
	rst 38h			;df37	ff 	. 
	rst 38h			;df38	ff 	. 
	rst 38h			;df39	ff 	. 
	rst 38h			;df3a	ff 	. 
	rst 38h			;df3b	ff 	. 
	rst 38h			;df3c	ff 	. 
	rst 38h			;df3d	ff 	. 
	rst 38h			;df3e	ff 	. 
	rst 38h			;df3f	ff 	. 
	rst 38h			;df40	ff 	. 
	rst 38h			;df41	ff 	. 
	rst 38h			;df42	ff 	. 
	rst 38h			;df43	ff 	. 
	rst 38h			;df44	ff 	. 
	rst 38h			;df45	ff 	. 
	rst 38h			;df46	ff 	. 
	rst 38h			;df47	ff 	. 
	rst 38h			;df48	ff 	. 
	rst 38h			;df49	ff 	. 
	rst 38h			;df4a	ff 	. 
	rst 38h			;df4b	ff 	. 
	rst 38h			;df4c	ff 	. 
	rst 38h			;df4d	ff 	. 
	rst 38h			;df4e	ff 	. 
	rst 38h			;df4f	ff 	. 
	rst 38h			;df50	ff 	. 
	rst 38h			;df51	ff 	. 
	rst 38h			;df52	ff 	. 
	rst 38h			;df53	ff 	. 
	rst 38h			;df54	ff 	. 
	rst 38h			;df55	ff 	. 
	rst 38h			;df56	ff 	. 
	rst 38h			;df57	ff 	. 
	rst 38h			;df58	ff 	. 
	rst 38h			;df59	ff 	. 
	rst 38h			;df5a	ff 	. 
	rst 38h			;df5b	ff 	. 
	rst 38h			;df5c	ff 	. 
	rst 38h			;df5d	ff 	. 
	rst 38h			;df5e	ff 	. 
	rst 38h			;df5f	ff 	. 
	rst 38h			;df60	ff 	. 
	rst 38h			;df61	ff 	. 
	rst 38h			;df62	ff 	. 
	rst 38h			;df63	ff 	. 
	rst 38h			;df64	ff 	. 
	rst 38h			;df65	ff 	. 
	rst 38h			;df66	ff 	. 
	rst 38h			;df67	ff 	. 
	rst 38h			;df68	ff 	. 
	rst 38h			;df69	ff 	. 
	rst 38h			;df6a	ff 	. 
	rst 38h			;df6b	ff 	. 
	rst 38h			;df6c	ff 	. 
	rst 38h			;df6d	ff 	. 
	rst 38h			;df6e	ff 	. 
	rst 38h			;df6f	ff 	. 
	rst 38h			;df70	ff 	. 
	rst 38h			;df71	ff 	. 
	rst 38h			;df72	ff 	. 
	rst 38h			;df73	ff 	. 
	rst 38h			;df74	ff 	. 
	rst 38h			;df75	ff 	. 
	rst 38h			;df76	ff 	. 
	rst 38h			;df77	ff 	. 
	rst 38h			;df78	ff 	. 
	rst 38h			;df79	ff 	. 
	rst 38h			;df7a	ff 	. 
	rst 38h			;df7b	ff 	. 
	rst 38h			;df7c	ff 	. 
	rst 38h			;df7d	ff 	. 
	rst 38h			;df7e	ff 	. 
	rst 38h			;df7f	ff 	. 
	rst 38h			;df80	ff 	. 
	rst 38h			;df81	ff 	. 
	rst 38h			;df82	ff 	. 
	rst 38h			;df83	ff 	. 
	rst 38h			;df84	ff 	. 
	rst 38h			;df85	ff 	. 
	rst 38h			;df86	ff 	. 
	rst 38h			;df87	ff 	. 
	rst 38h			;df88	ff 	. 
	rst 38h			;df89	ff 	. 
	rst 38h			;df8a	ff 	. 
	rst 38h			;df8b	ff 	. 
	rst 38h			;df8c	ff 	. 
	rst 38h			;df8d	ff 	. 
	rst 38h			;df8e	ff 	. 
	rst 38h			;df8f	ff 	. 
	rst 38h			;df90	ff 	. 
	rst 38h			;df91	ff 	. 
	rst 38h			;df92	ff 	. 
	rst 38h			;df93	ff 	. 
	rst 38h			;df94	ff 	. 
	rst 38h			;df95	ff 	. 
	rst 38h			;df96	ff 	. 
	rst 38h			;df97	ff 	. 
	rst 38h			;df98	ff 	. 
	rst 38h			;df99	ff 	. 
	rst 38h			;df9a	ff 	. 
	rst 38h			;df9b	ff 	. 
	rst 38h			;df9c	ff 	. 
	rst 38h			;df9d	ff 	. 
	rst 38h			;df9e	ff 	. 
	rst 38h			;df9f	ff 	. 
	rst 38h			;dfa0	ff 	. 
	rst 38h			;dfa1	ff 	. 
	rst 38h			;dfa2	ff 	. 
	rst 38h			;dfa3	ff 	. 
	rst 38h			;dfa4	ff 	. 
	rst 38h			;dfa5	ff 	. 
	rst 38h			;dfa6	ff 	. 
	rst 38h			;dfa7	ff 	. 
	rst 38h			;dfa8	ff 	. 
	rst 38h			;dfa9	ff 	. 
	rst 38h			;dfaa	ff 	. 
	rst 38h			;dfab	ff 	. 
	rst 38h			;dfac	ff 	. 
	rst 38h			;dfad	ff 	. 
	rst 38h			;dfae	ff 	. 
	rst 38h			;dfaf	ff 	. 
	rst 38h			;dfb0	ff 	. 
	rst 38h			;dfb1	ff 	. 
	rst 38h			;dfb2	ff 	. 
	rst 38h			;dfb3	ff 	. 
	rst 38h			;dfb4	ff 	. 
	rst 38h			;dfb5	ff 	. 
	rst 38h			;dfb6	ff 	. 
	rst 38h			;dfb7	ff 	. 
	rst 38h			;dfb8	ff 	. 
	rst 38h			;dfb9	ff 	. 
	rst 38h			;dfba	ff 	. 
	rst 38h			;dfbb	ff 	. 
	rst 38h			;dfbc	ff 	. 
	rst 38h			;dfbd	ff 	. 
	rst 38h			;dfbe	ff 	. 
	rst 38h			;dfbf	ff 	. 
	rst 38h			;dfc0	ff 	. 
	rst 38h			;dfc1	ff 	. 
	rst 38h			;dfc2	ff 	. 
	rst 38h			;dfc3	ff 	. 
	rst 38h			;dfc4	ff 	. 
	rst 38h			;dfc5	ff 	. 
	rst 38h			;dfc6	ff 	. 
	rst 38h			;dfc7	ff 	. 
	rst 38h			;dfc8	ff 	. 
	rst 38h			;dfc9	ff 	. 
	rst 38h			;dfca	ff 	. 
	rst 38h			;dfcb	ff 	. 
	rst 38h			;dfcc	ff 	. 
	rst 38h			;dfcd	ff 	. 
	rst 38h			;dfce	ff 	. 
	rst 38h			;dfcf	ff 	. 
	rst 38h			;dfd0	ff 	. 
	rst 38h			;dfd1	ff 	. 
	rst 38h			;dfd2	ff 	. 
	rst 38h			;dfd3	ff 	. 
	rst 38h			;dfd4	ff 	. 
	rst 38h			;dfd5	ff 	. 
	rst 38h			;dfd6	ff 	. 
	rst 38h			;dfd7	ff 	. 
	rst 38h			;dfd8	ff 	. 
	rst 38h			;dfd9	ff 	. 
	rst 38h			;dfda	ff 	. 
	rst 38h			;dfdb	ff 	. 
	rst 38h			;dfdc	ff 	. 
	rst 38h			;dfdd	ff 	. 
	rst 38h			;dfde	ff 	. 
	rst 38h			;dfdf	ff 	. 
	rst 38h			;dfe0	ff 	. 
	rst 38h			;dfe1	ff 	. 
	rst 38h			;dfe2	ff 	. 
	rst 38h			;dfe3	ff 	. 
	rst 38h			;dfe4	ff 	. 
	rst 38h			;dfe5	ff 	. 
	rst 38h			;dfe6	ff 	. 
	rst 38h			;dfe7	ff 	. 
	rst 38h			;dfe8	ff 	. 
	rst 38h			;dfe9	ff 	. 
	rst 38h			;dfea	ff 	. 
	rst 38h			;dfeb	ff 	. 
	rst 38h			;dfec	ff 	. 
	rst 38h			;dfed	ff 	. 
	rst 38h			;dfee	ff 	. 
	rst 38h			;dfef	ff 	. 
	rst 38h			;dff0	ff 	. 
	rst 38h			;dff1	ff 	. 
	rst 38h			;dff2	ff 	. 
	rst 38h			;dff3	ff 	. 
	rst 38h			;dff4	ff 	. 
	rst 38h			;dff5	ff 	. 
	rst 38h			;dff6	ff 	. 
	rst 38h			;dff7	ff 	. 
	rst 38h			;dff8	ff 	. 
	rst 38h			;dff9	ff 	. 
	rst 38h			;dffa	ff 	. 
	rst 38h			;dffb	ff 	. 
	rst 38h			;dffc	ff 	. 
	rst 38h			;dffd	ff 	. 
	rst 38h			;dffe	ff 	. 
	rst 38h			;dfff	ff 	. 
