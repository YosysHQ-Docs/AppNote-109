   /* ,         ,                                                     *
    * |\\\\ ////|  "EXOKAY: Exclusive access okay. Indicates that     *
    * | \\\V/// |   either the read or write portion of an exclusive  *
    * |  |~~~|  |   access has been succesful".                       *
    * |  |===|  |   Ref: A3.4.4 Read and write response structure,    *
    * |  |A  |  |   pA3-57, Table A3-4.                               *
    * |  | X |  |                                                     *
    *  \ |  I| /                                                      *
    *   \|===|/                                                       *
    *    '---'                                                        */
   property rdwr_response_exokay (valid, ready, resp);
      (valid && ready &&
       (resp == amba_axi4_protocol_checker_pkg::EXOKAY));
   endproperty // rdwr_response_exokay
