`default_nettype none
module invariant(input bit clk);
   bit rstn;
   bit packet_error;
   default clocking @(posedge clk); endclocking
   default disable iff(!rstn);
   seq #("__------------------") reset (clk, rstn);
`ifdef _ERROR_
   seq #("xx____x_____________") pkt_err (clk, packet_error);
`else
   seq #("xx__________________") pkt_err (clk, packet_error);
`endif
   ap_never: assert property (!packet_error);
endmodule // invariant
