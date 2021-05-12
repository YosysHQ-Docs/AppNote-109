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
the SystemVerilog specification language with the introduction of
*SystemVerilog 3.1a* and its goals of including both hardware design
and verification capabilities.

The difference between *SVA 3.1a* and other property specification
languages is that SVA is a native part of the SystemVerilog language,
and the assertions were no longer seen as interpreted comments but as
part of the language itself. The standardisation of the semantics
of SVA facilitated that different verification, emulation and formal
property checking EDA tools could standardize its implementation,
ensuring that all designs had the same results across different tools.
This increased the adoption of SVA in the industry.

In *SVA 3.1a*, both immediate and concurrent assertions were defined as
part of the standard. There were many conflicts and weaknesses in some
language features that were fixed in SVA2009. Different companies have
worked to improve the semantics and syntax of SVA to make it into how it
is today.

The SVA (SystemVerilog Assertions) specification is part of the P1800.
All the features of SystemVerilog regarding assertions are
specified by the Assertions Committee (SV-AC).

.. note::
    The SVA and PSL (Property Specification Language) are the results
    from different efforts that started with the standardisation of
    temporal logic for use in the hardware design and verification
    usage that *Accelera Formal Verification Technical Committee*
    started around 1998.

Introduction to SVA
-----------------------------------------
*What is an assertion*\  [1]_\ *?* - From the P1800, an assertion
*specifies a behavior of the system*. This term is confusing because is
similar to the definition of *property*. In fact, both *assert* and
*property* refer to the same thing. The inconsistency is mainly because
the term *assertion* is adopted in ABV, and *property* in FPV. BV is more
widely adopted, so the term assertion is used in a more "traditionalist" way.

Another way to define an assertion is as an unambiguous design behavior
expressed as a Boolean function or temporal expressions, that the design
must fulfill. Such property is usually described using a language that
can express behaviors of the design over time.

*Then, what is SVA?* - SVA is part of the P1800 and standardizes
assertion language semantics for SystemVerilog. That standard describes
the usage of a linear temporal logic [2]_ to define implementation
correctness of a design described with properties over Boolean-valued
functions and/or sequences that can be used to characterize the set of
states where such formula holds, using assertions. SVA can be used for
functional dynamic (simulation/emulation) and static (Formal Property
Verification) testing. The focus of *YosysHQ* are *static methods*,
therefore the description of SVA will be related to FPV.

As mentioned before, there is an *inconsistency* in the definition of the
building blocks of SVA that may lead to confusion. In the P1800, *assertion*
is defined as:

- **16. Assertions, 16.2 Overview, P364, Rev 2017:** "An assertion specifies
  a behavior of the system".
- **16. Assertions, 16.2 Overview, P364, Rev 2017:** "An assertion appears as
  an assertion statement that states the verification function to be performed".
- **16. Assertions, 16.2 Overview, P364, Rev 2017:** "[assertion kinds ...] assert,
  to specify the property as an obligation for the design that is to be checked to
  verify that the property holds".

Whereas property, is defined as:

- **16.12. Declaring properties, P420, Rev 2017:** "A property defines a behavior
  of the design".

So in short, an *assertion* is an affirmation or verification construct of a behavior
described using *properties* or the specification. Hoping to clear up this confusion, the
next section describes our interpretation of what SVA is.

.. note::
   Although SVA talks a lot about verification tasks, it can (and should) also be
   used by design engineers. In fact, in FPV all properties must be synthesizable,
   so they are more natural for a design engineer.
   Using SVA instead of comments to check some functionalities of the RTL,
   or some behaviors when a testbench is not available, can be very useful in the
   RTL bring-up, for example.

Re-Introduction to SVA
----------------------
The building block of SVA is the `property` construct, that not only
distinguishes an *immediate* from a *concurrent* assertion, but is the
actual element of the language where the behavior of the design is specified,
for example, using Boolean functions, sequences, and other expressions. SVA
introduces different kind of assertions discussed in the following sections.

Some benefits of SVA are:

* Enables protocols to be specified and verified using unambiguous constructs.
* Highly improves IP reuse. Interface assertions in the IP can be used as monitors
  for simulation/FPV to ensure correct integration.
* Reduces Time to Market (TTM).
* Assertions can be used instead of comments to document in a concise way design
  behaviors in a common and expressive language.

Among others.

There are two kinds of assertions: *immediate* and *concurrent*.
Immediate assertions are further divided into simple and deferred
immediate. Deferred immediate are subdivided into observed immediate and
final immediate assertions. Except from *Simple immediate* that are used
in SymbiYosys for the open source FPV framework, and concurrent assertions,
the rest are focused on simulation tasks. Immediate assertions are covered
in detail in **Appnote 105 Formal Property Checking Basics**.

+----------------------------------------------------------------------+
| .. image:: media/assertion_types.png                                 |
|    :width: 6.5in                                                     |
|    :height: 3.18in                                                   |
|    :align: center                                                    |
+======================================================================+
| Figure 1.1. A graphical description of the kinds of assertions.      |
+----------------------------------------------------------------------+

An example of a concurrent assertion is shown in *Figure 1.2*. This is
the kind of assertion commonly using in *Formal Property Verification
(FPV)*.

+----------------------------------------------------------------------+
| .. image:: media/assertion_struct.png                                |
|    :width: 6.5in                                                     |
|    :height: 2.93in                                                   |
|    :align: center                                                    |
+======================================================================+
| Figure 1.2. One possible definition of a concurrent SVA.             |
+----------------------------------------------------------------------+

As shown in Figure 1.2, the property has a verification layer with different
functions namely *assert*, *assume*, *cover* and *restrict* that are described
in <I want to do a link here, just writing a stub>.

===============
Assertion Types
===============

--------------------
Immediate Assertions
--------------------
Immediate assertions are pure combinatorial elements that do not allow for temporal domain events or sequences. Immediate assertions have the following properties:

- Non-temporal.

  - They are evaluated and reported at the same time (they cannot wait for any temporal time).

- Evaluation is performed immediately.

  - With the values sampled at the moment of activation of the assertion condition variables.

- Simpler evaluation semantics.

  - A clocked immediate assertion does not have the semantics of a concurrent assertion [3]_.

- Can be specified only in procedural blocks.

+----------------------------------------------------------------------+
| .. image:: media/immediate0.png                                      |
|    :width: 3.9in                                                     |
|    :height: 2.5in                                                    |
|    :align: center                                                    |
+======================================================================+
| Figure 1.3. Immediate assertion example, with clocked and unclocked  |
| semantics.                                                           |
+----------------------------------------------------------------------+

Immediate assertions are better described in **Appnote 105 Formal Property
Checking Basics**

---------------------
Concurrent Assertions
---------------------
The concurrent assertions capture sequences of events that span over time,
that is, they have a temporal domain that is evaluated at each clock tick
or time step of the system. A concurrent assertion rises the level of
abstraction of SystemVerilog due the transactional nature of this construct.

Only in terms of FPV, an immediate assertion could mimic a concurrent assertion
if certain helper logic is created such that it generates the notion of
*progress*. This logic of course may not be correct and can be quite complex
depending on the property expression to be described, so it needs to be verified
along with the property that this logic is supposed to describe. This method is
not suggested as it could add an extra verification task to the design, that can
be avoided using SVA.

.. note::
   This is one of the advantages of the *Tabby CAD Suite* over the Open Source
   Version: A leading-industry parser provides P1800 standard-compliant SV and
   SV-AC semantics for elaboration. So all the SystemVerilog constructs are
   enabled for the designer/validation engineer to use.

The Figure 1.4 shows an example of a concurrent assertion definition. This kind
of assertions can be defined in:

* *Initial* or *always* blocks.
* Inside a *module* or *checker* object.
* In a SystemVerilog *interface*.
* For simulation, in *progam* blocks.

+----------------------------------------------------------------------+
| .. image:: media/concurrent0.png                                     |
|    :width: 5.4in                                                     |
|    :height: 2.2in                                                    |
|    :align: center                                                    |
+======================================================================+
| Figure 1.4. Concurrent assertion example, defined in the procedural  |
| code and as standalone.                                              |
+----------------------------------------------------------------------+

===============
Elements of SVA
===============
----------
SVA Layers
----------
A concurrent property is composed primarily of four layers:

- Boolean.
- Temporal.
- Modeling.
- Verification.

These layers gives SVA full expressiveness. More details are discussed in the
following sections.

Boolean Layer
-------------
Concurrent properties can contain Boolean expressions that are composed of
SystemVerilog expressions with some restrictions. These expressions are used
to express conditions or behaviors of the design. Consider the Figure 1.5 that
represents the Boolean layer of a concurrent property extracted from AXI4-Stream.

+-------------------------------------------------------------------------+
| .. literalinclude:: ./child/0-keep_strb_rsvd.sv                         |
|     :language: systemverilog                                            |
|     :lines: 1-4                                                         |
+=========================================================================+
| Figure 1.5. The Boolean layer of the following property: "A combination |
| of TKEEP LOW and TSTRB HIGH must not be used (2.4.3 TKEEP and TSTRB     |
| combinations, p2-9, Table 2-2)." from AMBA IHI0051A.                    |
+-------------------------------------------------------------------------+

As can be seen, the evaluation of the Boolean expression shown in Figure 1.5
will be `logic one` when any combination of a TKEEP bit low and the same
bit in TSTRB high, otherwise the result will be `logic zero`.

Temporal Layer
--------------
The temporal layer express behaviors that can span over time, usually
expressed using SERE-regular _[5] expressions known as *sequences*.

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

Property Layer
--------------

Verification Layer
------------------

- **assert:** Specifies *validity*, *correctness*, or a behavior that a
  system or design is obligated to implement. When using the *assert*
  function, the solver's task is to either conclude that the assertion
  and the design are a *tautology* or to show a counterexample (CEX)
  indicating how the design violates or *contradicts* the assertion.
  **Behaviors are observed on the outputs of a Boolean functions,
  either design primary outputs or internal signals where some
  calculations of interest happens**. In short, The assertion w.r.t of
  a property must be true for all legal values applied at design inputs.
- **assume:** The property models how inputs of the design are driven
  in an unexamined way, that is, as a fact that the solver does not check
  but uses to *constraint* the valid values that will be used in the
  *primary inputs*. An assertion with related *input assumptions* when is
  proven, it is said that holds *assuming* that only the values constrained at
  the input are driven in the block under test. Modeling *assumptions* is one
  of the most error-prone tasks in formal verification that can cause some problems
  such as *vacuity* as described in *YosysHQ AppNote 120 -- Weak precondition
  cover and witness for SVA properties*. Assumption correctness is not checked by
  the formal tool.
- **cover:** Checks for satisfiability, that is, an evidence of whether any
  given behavior is implemented in the design. The main difference with the
  assertion statement is that when using the *cover* statement on a property,
  the proof succeed if there is *any* behavior in the design that the property
  dictates. For the proof under assertion directive, the behavior should be
  observed *for all* conditions in the inputs of the design.
- **restrict:** This directive is primarily used in FPV and is ignored in simulation.
  The *restrict* directive has similar semantics as *assume*, but is intended
  to use as delimiter in the state space, or in other words, to help in assertion
  convergence [4]_. For example, the *restrict* verification directive can be used to
  prove in a separated way, each arithmetic opcode (such as add, sub, etc). If the same
  environment is reused in simulation, the simulator will ignore the restriction.
  Otherwise, if an assumption had been used, the simulator would have failed because
  it cannot be guaranteed that certain opcode is the only one applied to the design.


Clock or time step
------------------

Disable condition
-----------------

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
   P1800 Language Reference Manual (LRM).

.. [3]
   Although the result of using one or the other in FPV may be the same,
   under certain circumstances, the way in which they are evaluated, for example,
   in simulation, is totally different. So this can create consistency problems
   in environments where the same assertions are used for both flows.

.. [4]
   Convergence in FPV is the process to have a full proof, which can be
   challenging for some designs.

.. [5] Sequential Extended Regular Expressions.