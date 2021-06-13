`default_nettype none
module relaxed_delay(input bit clk);
   bit foo;
   bit bar;
   bit rstn;
   default clocking @(posedge clk); endclocking
   default disable iff(!rstn);
   seq #("__------------------") reset (clk, rstn);
`ifdef _ERROR_
   seq #("__-__-__-_______-___") seq_foo(clk, foo);
   seq #("___-___-_--_----____") seq_bar(clk, bar);
`else
   seq #("__-__-__-_______-__-") seq_foo(clk, foo);
   seq #("___-___-_--_----_-__") seq_bar(clk, bar);
`endif
   ap_relaxed_delay: assert property (foo |-> ##[1:2] bar);
endmodule // invariant
