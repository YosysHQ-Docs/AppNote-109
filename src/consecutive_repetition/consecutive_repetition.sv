`default_nettype none
module consecutive_repetition #(parameter BA_WIDTH=8)
   (input bit clk, input bit [BA_WIDTH-1:0] bank, nd_bank);
   localparam bit [2:0] tWR = 3'b100;
   localparam bit [1:0] PRE = 2'b01;
   localparam bit [1:0] WR  = 2'b10;
   bit [1:0] 		cmd;
   bit 			wr;
   bit 			rstn;
   default clocking @(posedge clk); endclocking
   default disable iff(!rstn);
   seq #("_-------------------") reset (clk, rstn);
`ifdef _ERROR_
   //     0123456789ABCDEF0123
   seq #("03200000200001200100", 2) seq_cmd(clk, cmd);
`else
   seq #("03200000200001200000", 2) seq_cmd(clk, cmd);
`endif
   /* Conceptually nd_bank is any possible value in the range
    * of BA_WIDTH-1. So this variable test all possible banks
    * of the SDRAM, in all possible conbinations, instead of
    * using a fixed value. The nd_bank is a (free) primary input */
   nd_bank_select: assume property($stable(nd_bank));
   /* Main property */
   let CMDWR = (cmd == WR && bank == nd_bank);
   let notCMDPRE = !(cmd == PRE && bank == nd_bank);
   cmdWR_to_cmdPRE: assert property (CMDWR |-> ##1 notCMDPRE[*tWR]);
endmodule // invariant
