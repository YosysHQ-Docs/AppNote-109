`default_nettype none
module systemf_sv(input bit clk);
   bit rstn;
   bit a;
   bit b;
   bit c;
   bit d;
   
   default clocking @(posedge clk); endclocking
   default disable iff (!rstn);
   
   // If a is true in the current clock cycle it must be true
   // in the previous cycle as well.
   seq #("_-------------------") reset (clk, rstn);
   seq #("_-------------------") seq_a(clk, a);
`ifdef _ERR_
   ap_past: assert property($past(a));
`else
   ap_past: assert property(##1 $past(a));
`endif
   
   // If b becomes 1, it must be 1 for the next 5 clock cycles
   seq #("-------____________-") seq_b(clk, b);
   ap_rose: assert property($rose(b) |=> b[*4]);
   cp_rose: cover property($rose(b) ##1 b[*4]);
   
   // If c becomes low, it must be low for the next 5 clock cycles
   seq #("------------------__") seq_c(clk, c);
   ap_fell: assert property($fell(c) |=> c[*4]);
   cp_fell: cover property($fell(c) ##1 c[*4]);

   // d toggles forever
   seq #("_-_-_-_-_-_-_-_-_-_-") seq_d(clk, d);
   ap_changed: assert property(<implement the assertion>);
   
endmodule // systemf_sv
