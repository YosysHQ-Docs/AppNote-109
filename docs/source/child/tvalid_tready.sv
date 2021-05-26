   /* ,         ,                                                     *
    * |\\\\ ////| "Once TVALID is asserted it must remain asserted    *
    * | \\\V/// |  until the handshake (TVALID) occurs".              *
    * |  |~~~|  |  Ref: 2.2.1. Handshake Protocol, p2-3. 	      *
    * |  |===|  |						      *
    * |  |A  |  |						      *
    * |  | X |  |						      *
    *  \ |  I| /						      *
    *   \|===|/							      *
    *    '---'							      */
   property tvalid_tready_handshake;
      @(posedge ACLK) disable iff (!ARESETn)
	TVALID && !TREADY |-> ##1 TVALID;
   endproperty // tvalid_tready_handshake
