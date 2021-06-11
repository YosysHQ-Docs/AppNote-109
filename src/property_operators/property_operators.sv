`default_nettype none
module property_operators(input bit clk);
   bit en;
   bit a;
   bit b;
   bit c;
   bit d;
   bit rstn;
   default clocking @(posedge clk); endclocking
   default disable iff(!rstn);
   seq #("__------------------") reset (clk, rstn);
`ifdef _ERROR_
   seq #("____--____----------") seq_en(clk, en);
   seq #("_____-_-_-----------") seq_a(clk, a);
   seq #("_____-------__------") seq_b(clk, b);
   seq #("_______-------______") seq_c(clk, c);
   seq #("______________--____") seq_d(clk, d);
`endif
   ap_nexttime: assert property (en |-> nexttime a);
   ap_always: assert property(en |=> always b);
   ap_until: assert property(en |=> c until d);
endmodule // invariant
