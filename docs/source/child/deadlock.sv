   // Deadlock (ARM Recommended)
   /* ,         ,                                                     *
    * |\\\\ ////|  It is recommended that READY is asserted within    *
    * | \\\V/// |  MAXWAITS cycles of VALID being asserted.           *
    * |  |~~~|  |  This is a *potential deadlock check* that can be   *
    * |  |===|  |  implemented as well using the strong eventually    *
    * |  |A  |  |  operator (if the required bound is too large to be *
    * |  | X |  |  formally efficient). Otherwise this bounded        *
    *  \ |  I| /   property works fine.                               *
    *   \|===|/                                                       *
    *    '---'                                                        */
   property handshake_max_wait(valid, ready, timeout);
      valid & !ready |-> ##[1:timeout] ready;
   endproperty // handshake_max_wait

   // Deadlock (ARM Recommended)
   /* ,         ,                                                     *
    * |\\\\ ////|  It is recommended that READY is asserted within    *
    * | \\\V/// |  MAXWAITS cycles of VALID being asserted.           *
    * |  |~~~|  |  This is a *potential deadlock check* that can be   *
    * |  |===|  |  implemented as well using the strong eventually    *
    * |  |A  |  |  operator (if the required bound is too large to be *
    * |  | X |  |  formally efficient). Otherwise this bounded        *
    *  \ |  I| /   property works fine.                               *
    *   \|===|/                                                       *
    *    '---'                                                        */
   property handshake_max_wait(valid, ready, timeout);
      valid & !ready |-> strong(##[1:$]) ready;
   endproperty // handshake_max_wait
