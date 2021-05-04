===============================================
Property Checking with SystemVerilog Assertions
===============================================

--------
Abstract
--------
TBD

------------
Organisation
------------
TBD

------------
Introduction
------------

Brief history of SystemVerilog Assertions
-----------------------------------------

Assertion Based Verification (ABV) is considered an efficient
verification methodology of ASIC/SoC designs. This methodology is based
on instrumenting the design with assertions that were considered in the
past as executable comments that could be verified in simulation,
emulation and formal property verification. These assertions served as
a documentation of the design as well, being sometimes preferred over
comments inlined in the RTL constructs.

Many assertion language specifications were developed to address the
different verification needs with ABV. For example, ForSpec, OVA, ‘e’
and Sugar. These language specifications were not part of hardware
design languages such as VHDL or Verilog mainly because they were
considered as languages of different purposes.

The *SVA 3.1a* assertion specification was born as an integral part of
the SystemVerilog specification language With the introduction of
*SystemVerilog 3.1a* and its goals of including both hardware design
and verification capabilities.

The difference between *SVA 3.1a* and other property specification
languages is that SVA is a native part of the SystemVerilog language,
and the assertions were no longer seen as interpreted comments but as
part of the language itself. The standardisation of the semantics
of SVA facilitated that different verification, emulation and formal
property checking EDA tools could standardize its implementation,
ensuring that all designs had the same results accross different tools.
This increased the adoption of SVA in the industry.

In *SVA 3.1a*, both immediate and concurrent assertions were defined as
part of the standard. There were many conflicts and weaknesses in some
language features that were fixed in SVA2009. Different companies have
worked to improve the semantics and syntax of SVA to make it into how it
is today.

The SVA (SystemVerilog Assertions) specification is part of the IEEE
1800-2012. All the features of SystemVerilog regarding assertions are
specified by the Assertions Committee (SV-AC).

.. note::
    The SVA and PSL (Property Specification Language) are the results
    from different efforts that started with the standardisation of
    temporal logic for use in the hardware design and verification
    usage that *Accelera Formal Verification Technical Committee*
    started around 1998.

-----------------------------------------
Introduction to SVA
-----------------------------------------
*What is an assertion*\  [1]_\ *?* - From the IEEE 1800, an assertion
*specifies a behavior of the system*. This term is confusing with the
definition of *property*. Another way to define an assertion is as a
design statement expressed as Boolean function or property that the
design must fulfill. The property is usually described using a language
that can express actions of the design over time.

An example of the semantical components of a concurrent assertion is shown
in *Figure 1.1*. This is the kind of assertion commonly using in *Formal
Property Verification (FPV)*. Assertions and their types will be described
in the following sections.

+----------------------------------------------------------------------+
| .. image:: media/assertion_struct.png                                |
|    :width: 6.5in                                                     |
|    :height: 2.93in                                                   |
|    :align: center                                                    |
+======================================================================+
| Figure 1.1. The witness is the assertion logic (antecedent and       |
| consequent) converted into a cover statement, whereas the weak       |
| precondition is just a precondition reachability test with limited   |
| visibility.                                                          |
+----------------------------------------------------------------------+

As shown in Figure 1.1, there are three verification functions that an
assertion performs:

- **assert**: Specifies *validity*, *correctness* or a behavior that a system
      or design is obligated to implement. When using the *assert*
      function, the solver's task is to either conclude that the
      assertion and the design are a *tautology* or to show a
      counterexample (CEX) indicating how the design violates *(contradicts)* the
      assertion. **Behaviors are observed on the outputs of a Boolean function,
      either design primary outputs or internal signals where some calculations
      of interest happens**.
- **assume**: 
- **cover:**
- **restrict**:

*Then, what is SVA?* - SVA is part of the IEEE 1800 and standarises
assertion language semantics for SystemVerilog. That standard describes
the usage of a linear temporal logic [2]_ to define implementation
correctness of a design described with properties over Boolean-valued
functions and/or sequences that can be used to characterise the set of
states where such formula holds, using assertions. SVA can be used for
functional dynamic (simulation/emulation) and static (Formal Property
Verification) testing. The focus of YosysHQ are *static methods*, therefore
the description of SVA will be related to FPV.

---------------
Assertion Types
---------------

Immediate Assertions
--------------------

There are two kinds of assertions: *immediate* and *concurrent*.
Immediate assertions are further divided into simple and deferred
immediate. Deferred immediate are subdivided into observed immediate and
final immediate assertions. Except from *Simple immediate* that are used
(solely) in SymbiYosys for FPV [3]_, the rest of the assertions are focused
on simulation tasks.

Immediate assertions are covered in detail in **Appnote 105 Formal Property 
Checking Basics**.

+----------------------------------------------------------------------+
| .. image:: media/assertion_types.png                                 |
|    :width: 6.5in                                                     |
|    :height: 3.18in                                                   |
|    :align: center                                                    |
+======================================================================+
| Figure 1.2. A graphical description of the kinds of assertions.      |
+----------------------------------------------------------------------+

Concurrent Assertions
---------------------

Formal Property Verification uses SystemVerilog assertions to describe
events and properties that a design should satisfy in a model. The model
is the design in RTL and together with the properties in SVA, is
converted into a format or structure suitable for static analysis (for
example a state and transition diagrams). This structure or format is
the input of a solver, which is the entity in charge of validating or
refuting said properties using mathematical techniques.

The most common constructs to specify the design behavior are assert,
assume and cover statements, and their types are immediate and
concurrent. Concurrent properties are activated at each main dynamic
event (such as the system clock) and the semantics are based on such
events, whereas the immediate properties do not depend on a dynamic
event (unclocked) and they behave as an if statement.

Immediate and Concurrent Assertions for FPV

An assertion is an obligation of the system, that is, the property
behavior must be **valid** under all circumstances (possible inputs) and
if this behavior is violated, the tool will output a waveform showing
the sequence of inputs leading to the violation. On the other hand, if
the property succeeds, no waveform is generated. The cover is a
statement that checks if a specified behavior is **satisfiable** in the
current system, and if such behavior exists, the tool will show a
waveform with the inputs leading to that state (this sequence of inputs
is one of many possible interpretations that could exist in the design).
Finally, assumptions express that a statement is assumed to hold, this
is not a check but a restriction given to a model, for example, to the
design inputs that are used to constraint the verification to a specific
scenarios (an assumption can be used to constrain two inputs that are
expected to be driven in a mutually exclusive manner by a neighbor
block). Assumption correctness is not checked by the formal tool.

+----------------------------------------------------------------------+
| +----------------------------------------------------------------+   |
| | assign b = a;                                                  |   |
| |                                                                |   |
| | // if a is true then must be true b (edge-sensitive version)   |   |
| |                                                                |   |
| | always_ff @(posedge clk) immediate0: assert (b == a);          |   |
| |                                                                |   |
| | // if a is true then must be true b (level-sensitive version)  |   |
| |                                                                |   |
| | always_comb immediate1: assert (b == a);                       |   |
| +================================================================+   |
| | // if a is true then must be true b (or “a” follows “b”)       |   |
| |                                                                |   |
| | concurrent0: assert property (@(posedge clk) !a \|\| b);       |   |
| |                                                                |   |
| | // same but using overlapping implication operator \|->        |   |
| | described below                                                |   |
| |                                                                |   |
| | concurrent1: assert property (@(posedge clk) a \|-> b);        |   |
| +----------------------------------------------------------------+   |
+======================================================================+
| Figure N. Immediate (upper side) and concurrent (lower side)         |
| assertions. The concurrent assertion semantics are equivalent to the |
| implication operation that will be discussed later in this post.     |
+----------------------------------------------------------------------+

Clocks and Resets

The default clock event for a sequential property can be defined using
the keyword **default clocking** and serves as the leading clock for all
the concurrent properties. Likewise, some properties may need to be
disabled in some events, because their results are not valid anyway, for
example, during the reset state. The **default disable iff (event)**
keywords can be used for this.

In this example of a simple property from a PIPE interface, to state
that all concurrent properties are checked each *posedge* PCLK and
disabled if the *PRSTn* reset is deasserted, the following SystemVerilog
definition is employed.

+----------------------------------------------------------------------+
| // Concurrent properties are checked each *posedge* PCLK             |
|                                                                      |
| default clocking formal_clock                                        |
|                                                                      |
| @(posedge PCLK);                                                     |
|                                                                      |
| endclocking                                                          |
|                                                                      |
| // And disabled if the *PRSTn* reset is deasserted                   |
|                                                                      |
| default disable iff (!PRSTn);                                        |
|                                                                      |
| property_a: assert property (RxStatus == 3’b011 \|-> ##1             |
| Receiver_detected); // The property does not need to explicitly      |
| define PCLK as main clock and !PRSTn as disable event, as it is      |
| defined in the default clocking and disable blocks.                  |
+======================================================================+
| Figure N. Usage of default clocking and default reset                |
+----------------------------------------------------------------------+

SystemVerilog Sequences

Sequences can be more complex than just Boolean values. Basic sequences
can contain single delays (for example ##1 means one cycle delay) and
bounded/unbounded range delays (the bounded sequence ##[1:10] means one
to ten cycles later, the unbounded sequence ##[+] means one or more
cycles later). Sequences can be enclosed within sequence … endsequence
SVA constructs, or described directly in the property block. More basic
and advanced sequences exist, but the description of them is outside of
the scope of this document.

For example, consider the following system requirement encoded as a
property from the `AMBA 5 CHI
Specification <https://developer.arm.com/documentation/ihi0050/c>`__,
Figure 13-6: “If the tx_fsm transmit link sequence is TxStop, TxAct,
TxRun, TxDeact and TxStop, the output the tx_link_ok will be asserted
one cycle later. Each state transition must be performed between 1 and 4
clock cycles”. This statement can be partitioned as shown below:

+--------------------------------------+
| +----------------------------------+ |
| | **Sequence (antecedent/cause):** | |
| |                                  | |
| | *tx_fsm == TxStop ##[1:4],*      | |
| |                                  | |
| | *tx_fsm == TxAct ##[1:4],*       | |
| |                                  | |
| | *tx_fsm == TxRun ##[1:4],*       | |
| |                                  | |
| | *tx_fsm == TxDeact ##[1:4],*     | |
| |                                  | |
| | *tx_fsm == TxStop ##[1:4]*       | |
| +==================================+ |
| | **Effect (consequent):**         | |
| |                                  | |
| | *##1 tx_link_ok == 1’b1*         | |
| +----------------------------------+ |
+======================================+
| Figure N.                            |
+--------------------------------------+


Now, to connect both cause and effect (or antecedent and consequent) the
*implication* operation (|-> non-overlapping, \|=> overlapping) is used.
For example, the sentence “When input a is set, b must also be set one
cycle later” is expressed using the implication operation as follows:

+----------------------------------------------------------------------+
| a_implies_b: assert property (a \|-> ##1 b); // Overlapping operator |
|                                                                      |
| a_implies_b: assert property (a \|=> b); // Non-overlapping operator |
+======================================================================+
| Figure N.                                                            |
+----------------------------------------------------------------------+

With this information, the property “If the tx_fsm transmit link
sequence is TxStop, TxAct, TxRun, TxDeact and TxStop, the output the
tx_link_ok will be asserted one cycle later. Each state transition must
be performed between 1 and 4 clock cycles” can be described as follows:

+------------------------------------------------------------------------+
| *tx_full_path: assert property (@(posedge ACLK) disable if (!ARESETn)* |
|                                                                        |
| *tx_fsm == TxStop ##[1:4],*                                            |
|                                                                        |
| *tx_fsm == TxAct ##[1:4],*                                             |
|                                                                        |
| *tx_fsm == TxRun ##[1:4],*                                             |
|                                                                        |
| *tx_fsm == TxDeact ##[1:4],*                                           |
|                                                                        |
| *tx_fsm == TxStop ##[1:4] \|-> ##1 tx_link_ok == 1’b1);*               |
+========================================================================+
| Figure N.                                                              |
+------------------------------------------------------------------------+

This property in SVA describes easily a transition of events that
otherwise may be implemented in a (System)Verilog FSM and shows one of
the advantages of SVA over the open source version of SBY.

.. [1]
   Unfortunately, the definition of “assertion” is not consistent in the
   industry, and is often used interchangeably with the term “property”.

.. [2]
   SystemVerilog Assertions are temporal logics and model checking
   methods applied to real world hardware design and verification. In
   fact, most of the notations from the literature that describe these
   methods are employed to express the formal semantics of SVA in the
   IEEE 1800 Language Reference Manual (LRM).

.. [3]
   Arguably there is another EDA tool that supports immediate assertions for
   static functional verification (another term for FPV). However, this
   tool is not opensource and supporting immediate assertions is not their
   goal.
