// Concurrent properties are checked each *posedge* PCLK
default clocking
   formal_clock @(posedge PCLK);
endclocking

// And disabled if the *PRSTn* reset is deasserted
default disable iff (!PRSTn);

/* The property does not need to explicitly
 * define PCLK as main clock and !PRSTn as disable event, as it is
 * defined in the default clocking and disable blocks. */
property_a: assert property (RxStatus == 3’b011 |-> ##1
			     Receiver_detected);
