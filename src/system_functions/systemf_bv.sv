`default_nettype none
module systemf_bv(input bit clk);
   logic rstn;
   logic a;
   logic [1:0] b;

   default clocking @(posedge clk); endclocking
   default disable iff (!rstn);

   // All bits of a must be set to zero
   seq #("_-------------------") reset (clk, rstn);
`ifdef _ERR_
   seq #("__________________-_") seq_a(clk, a);
`else
   seq #("____________________") seq_a(clk, a);
`endif
   ap_countbits: assert property($countbits(a, '1) == 1'b0);
   ap_countones: assert property($countones(a) == 1'b0);
   
   // Full/Empty must not appear at the same time
`ifdef _ERR_
   seq #("00000000000000000000", 2) seq_b(clk, b);
`else
   seq #("12112211122221122211", 2) seq_b(clk, b);
`endif
   ap_onehot0: assert property($onehot0(b));
   ap_onehot: assert property($onehot(b));
endmodule // systemf_bv
