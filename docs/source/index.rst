===============================================
Property Checking with SystemVerilog Assertions
===============================================

--------
Abstract
--------
This Application Note was written with the intention of
showing a brief introduction to SVA, and is definitely not
a substitute for extensive training. To learn more about
formal verification and SVA, it is recommended to book the
course given by FPV specialists at YosysHQ.

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
    temporal logics for use in the hardware design and verification
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

.. note::
   SVA supports both white-box and black-box verification.

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
in `I want to do a link here, just writing a stub <tbd>` __.

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

Clock or time step
------------------
Concurrent assertions are associated with a *clock* which defines the
sampling clock or the point in time where the assertion is evaluated. This
construct helps to explicitly define the event for sampled valued
functions as well, that will be discussed in next sections.
The default clock event for a concurrent property can be defined using
the keyword `default clocking` and serves as the leading clock for all
the concurrent properties. The Figure 1.5 shows an example of default
clocking definition.

Disable condition
-----------------
Likewise, some properties may need to be disabled during some events,
because their results are not valid anyway, for example, during the
reset state. The **default disable iff (event)** keywords can be used
to define when a concurrent assertion result is not intended to be
checked. The Figure 1.5 shows an example of default reset definition.

+----------------------------------------------------------------------+
| .. literalinclude:: ./child/pipe.sv                                  |
|     :language: systemverilog                                         |
|     :lines: 1-13                                                     |
+======================================================================+
| Figure 1.4. Usage of default clocking and default disable events used|
| to state that all concurrent properties are checked each *posedge*   |
| PCLK and disabled if the *PRSTn* reset is deasserted.                |
+----------------------------------------------------------------------+

===============
Elements of SVA
===============
----------
SVA Layers
----------
A concurrent property is composed primarily of four layers:

- Boolean layer.
- Temporal or Sequence layer.
- Property layer.
- Verification layer.

These layers gives SVA full expressiveness. More details are discussed in the
following sections.

Boolean Layer
-------------
Concurrent properties can contain Boolean expressions that are composed of
SystemVerilog constructs with some restrictions _[5]. These expressions are used
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

Temporal or Sequence Layer
--------------------------
The temporal layer express behaviors that can span over time, usually
expressed using SERE-regular _[6] expressions known as *sequences* that
describes sequential behaviors that are employed to build properties.

SVA provides a set of powerful temporal operators that can be used to
describe complex behaviors or conditions in different points of time.

Sequences can be more complex than just Boolean values. Basic sequences
can contain single delays (for example `##1` that means one cycle delay) and
bounded/unbounded range delays (the bounded sequence `##[1:10]` means one
to ten cycles later, the unbounded sequence `##[+]` means one or more
cycles later). Sequences can be enclosed within `sequence … endsequence`
SVA constructs, or described directly in a property block.

A sequence can be seen as a description that defines values over time,
and unlike *properties* or *Boolean functions*, a sequence does not have
true or false values but *matches* or *tight satisfaction* points. For
example, the sequence *foo is followed by bar in one or two cycles* expressed
in SVA as:

.. code-block:: systemverilog

   foo ##[1:2] bar

Is shown in Figure 1.6. As can be seen, there may be different match or tight
satisfaction points:

* When *foo* is true at cycle t2 and bar at cycle t3.
* When *foo* is true at cycle t2 and bar at cycle t4.
* When *foo* is true at cycle t2 and bar is true at cycle t3 and t4.

There is also a case where sequence does not match, which is when
*foo* is true at cycle t2 but *bar* is not seen during the next
one or two cycles.

+----------------------------------------------------------------------+
| .. image:: media/first_seq.png                                       |
|    :width: 10.05cm                                                   |
|    :height: 10.85cm                                                  |
|    :align: center                                                    |
+======================================================================+
| Figure 1.6. Example of sequence `foo ##[1:2] bar`.                   |
+----------------------------------------------------------------------+

Sequences can be promoted to sequential properties if they are used in a
property context (in other words, when used in property blocks). Starting
from SV09, *weak* and *strong* operators have been defined.
*Strong* sequential properties hold if there is a non-empty match of the
sequence (it must be witnessed), whereas a *weak* sequence holds if there
is no finite prefix witnessing a no match (if the sequence never happens,
the property holds).

*Strong* sequential properties are identified by the prefix *s_* as
in:
* s_eventually.
* s_until.
* s_until_with.
* s_always.

Or enclosed within parenthesis followed by the keyword *strong* as in:
* strong(s ##[1:10] n).

The evaluation of sequential properties (if they are weak or strong) when the
*weak* or *strong* operands are omitted depends on the verification directive
where they are used:

* **Weak** when the sequence is used in *assert* or *assume* directive.
* **Strong** in all other cases.

Some sequential property operators are discussed below.

Basic Sequence Operators Introduction
-------------------------------------

Bounded Delay Operator
----------------------

The bounded operators `##m` and `##[m:n]` where *m* and *n* are non-negative integers,
can be used to specify clock delays between two events. The Figure 1.6 is
an example of usage of these operators. For the following sequence:

.. code-block:: systemverilog

   foo ##m bar

If *m == 1* the sequence is split in two adjacent fragments, *concatenating*
both *foo* and *bar* expressions. If *m == 0* both *foo* and *bar* overlaps,
creating a *fusion* of both expressions. The sequence concatenation starts
matching *bar* in the next clock cycle after *foo* matches. Whereas for
sequence fusion, both *foo* and *bar* start matching at the same clock tick
where *foo* matches. See Figure 1.7 for a better understanding.

+-------------------------------------------------------------------------+
| .. image:: media/concat_fusion.png                                      |
|    :width: 10.05cm                                                      |
|    :height: 5.29cm                                                      |
|    :align: center                                                       |
+=========================================================================+
| Figure 1.7. Illustration of sequence fusion and sequence concatenation. |
+-------------------------------------------------------------------------+

For a more concise example, consider the Figure 14-5 Combined Tx and Rx
state machines from ARM IHI 0050E. To describe the transitions of the Tx Link
FSM the following sequence can be defined:

.. code-block:: systemverilog

   /* TX FSM should transition from TxStop
    * to TxAct in one to four cycles. And
    * in the same way with the other states
    * of the FSM, fulfilling the transitions
    * shown in Figure 14-5. */
   sequence tx_link_full;
     fsm_lnk_ns.chi_tx_t == TxStop  ##[1:4]
     fsm_lnk_ns.chi_tx_t == TxAct   ##[1:4]
     fsm_lnk_ns.chi_tx_t == TxRun   ##[1:4]
     fsm_lnk_ns.chi_tx_t == TxDeact ##[1:4]
     fsm_lnk_ns.chi_tx_t == TxStop  ##[1:4]
   endsequence

This sequence *tx_link_full* describes the transition of the Tx Link FSM from TxStop
up to TxStop that precedes TxDeact. This sequence can be used in a cover or assert
construct to verify that the design implements correctly the Tx Link, or to show
a witness of this transition. For example, to find a trace in a design where these
transitions are fulfilled, a cover construct such as the one shown below can be employed:

.. code-block:: systemverilog

    wp_full_tx: cover property (@(posedge ACLK) disable iff (!ARESETn) tx_link_full);


.. note::
   For FPV, it is always recommended to keep the cycle window small as possible
   since this impacts the performance of the proof.


Unbounded Delay Operator
------------------------
There are two operators for relaxed delay requirements:

* Zero or more clock ticks: `##[0:$]` (or the shorcut `##[*]`).
* One or more clock ticks: `##[1:$]` (or the shorcut `##[+]`).

The formal semantics are the same as in the bounded delay operator. These operators
are useful, for example, to check forward progress of safety
properties that could be satisfied *by doing nothing*. What does this means?, consider
the VALID/READY handshake defined in **ARM IHI 0022E Page A3-9** (better known as
AXI-4 specification). A potential deadlock can happen when VALID signal is asserted
but READY is never asserted. If the property shown in Figure 1.8 is part of a design
where READY is deasserted forever after VALID has been asserted, the property will
pass vacuously.

+----------------------------------------------------------------------+
| .. literalinclude:: ./child/rdwr_response_exokay.sv                  |
|     :language: systemverilog                                         |
|     :lines: 1-14                                                     |
+======================================================================+
| Figure 1.8. A property that monitors the EXOKAY response value when  |
| VALID and READY are asserted.                                        |
+----------------------------------------------------------------------+

To check that the system is actually making progress, the property using *one or
more clock ticks* operator shown in Figure 1.9 can be used. If this property fails,
then the FPV user can deduce that property of Figure 1.8 is not healthy.

+----------------------------------------------------------------------+
| .. literalinclude:: ./child/deadlock.sv                              |
|     :language: systemverilog                                         |
|     :lines: 1-14                                                     |
+======================================================================+
| Figure 1.9. A property that checks for a deadlock condition. If VALID|
| is asserted and READY is not asserted in *timeout* non-negative      |
| cycles, the property will be unsuccessful.                           |
+----------------------------------------------------------------------+

.. note::
   The property of Figure 1.9 can still fail in certain scenarios. This is
   because the unbounded operator employed in the property definition has
   weak semantics. A better solution could be to make this property *strong*
   but this implies that this *safety* property will be converted into a *liveness*
   one. Liveness and safety concepts are described in *Property Layer* section.

Consecutive Repetition
----------------------
Imagine the following property from an SDRAM controller (JESDEC 21-C): The WR (write) command
can be followed by a PRE (precharge) command in a minimum of tWR cycles. If *tWR == 15*
then the property can be described as follows:

.. code-block:: systemverilog

    let notCMDPRE = (!cmd == PRE) && bank == nd_bank;
    // notCMDPRE must hold 15 times after WR command is seen
    property cmdWR_to_cmdPRE;
      cmd == WR && bank == nd_bank |-> ##1 notCMDPRE ##1 notCMDPRE ##1 notCMDPRE
                                       ##1 notCMDPRE ##1 notCMDPRE ##1 notCMDPRE
                                       ... ##1 notCMDPRE ##1 notCMDPRE;
    endproperty

This is too verbose and not an elegant solution. SVA has a construct to define that
an expression must hold for *m* consecutive cycles: the consecutive repetition
operator *[\*m]*. The same property can be described using the consecutive
repetition operator as follows:

.. code-block:: systemverilog

    let notCMDPRE = (!cmd == PRE) && bank == nd_bank;
    // notCMDPRE must hold 15 times after WR command is seen
    property cmdWR_to_cmdPRE;
      cmd == WR && bank == nd_bank |-> ##1 notCMDPRE [*15];
    endproperty

And if the tWR value is set as a parameter, then this can be further reduced to:

.. code-block:: systemverilog

   cmd == WR && bank == nd_bank |-> ##1 notCMDPRE [*tWR];

.. note::
   The *nd_bank* expression is a non-deterministic value choosen by the
   formal solver as a symbolic variable. A symbolic variable is a variable
   that takes any valid value in the initial state and then is kept stable.
   This variable is useful to track a single arbitrary instance of a design
   where properties are defined for multiple symmetric units.

As with delay operators, sequence repetition constructs have some variants
such as:

* **Consecutive repetition range `s[\*m:n]`**: The sequence *s* occurs from
  m to n times.
* **Infinite repetition range `s[\*]`**: The sequence *s* is repeated zero or more times.
* **Infinite repetition range `s[+]`**: The sequence *s* is repeated one or more times.
* **Nonconsecutive repetition operator `s[=m:n]`**: The sequence *s* occurs
  exactly from n to m times and *s is not required to be the last element*.
* **GoTo repetition operator `s[->m:n]`**: The sequence *s* occurs
  exactly from n to m times and *s is required to be the last element*.

.. note::
   Not all sequential property operators are FPV friendly:

   * GoTo and nonconsecutive operators.
   * Throughout.
   * Intersect.
   * first_match().
   * Within.
   * Etc.

   These operators increases the complexity of the model and may cause that some
   assertions not converge.


Property Layer
--------------
The property layer is where all the expressiveness of SVA starts to take shape. In
this layer, Boolean constructs, sequences and property operators are used to
encapsulate the behavior of the design within `property ... endproperty` blocks
that will be further utilised by the *verification layer* to perform certain task.

A property construct can have formal arguments as shown in Figure 1.8 and Figure 1.9,
that are expanded when the property is instantiated with the proper arguments. Properties
can also have no arguments.

The P1800 defines several kinds of properties of which some are shown below:

* **Sequence**: As described in Section Temporal or Sequence Layer, a sequence
  property have three forms namely *sequence_expression*, *weak(sequence_expression)*
  and *strong(sequence_expression)*. Remember that a sequence is promoted to a sequence
  property if the sequence expression is used in property context.
* **Negation**: This property uses the **not** *property_expression* operator to basically
  evaluate to true if *property_expression* is false.
* **Disjunction**: A property of the form *property_expression1* **or**
  *property_expression2* evaluates to true if at least one of the property expressions
  evaluates to true.
* **Conjunction:**: A property of the form *property_expression1* **and**
  *property_expression2* evaluates to true if the two property expressions
  evaluates to true.
* **If-else**: This property has the form **if (condition)** *property_expression1* **else**
  *property_expression2* and can be seen as a mechanism to select a valid property based on
  a certain condition.
* **Implication**: One of the most used kinds of properties in ABV. This property has the
  form **sequence_expression** *|=> or |->* **property_expression** that connects the cause
  (expression in LHS or antecedent) to an effect (expression in RHS or consequent).
  More about this type of property is described in **YosysHQ AppNote 120 -- Weak
  precondition cover and witness for SVA properties.**

The rest of the kinds of properties are better explained with a graph as shown
below.

.. note::
   There are different versions of the following properties. Refer to **P1800
   (2017) Section 16.12 Declaring properties** for more information.

**Nexttime property**
This property evaluates to true if the property expression *p* is true
in the next clock cycle.

+-------------------------------------------------------------------------+
| .. image:: media/nexttime.png                                           |
|    :width: 15.92cm                                                      |
|    :height: 6.46cm                                                      |
|    :align: center                                                       |
+=========================================================================+
| Figure 1.10. The property *nexttime p*  holds if *p* is true in the next|
| clock cycle.                                                            |
+-------------------------------------------------------------------------+


**Always property**
This property evaluates to true if the expression *p* holds at all states.

+-------------------------------------------------------------------------+
| .. image:: media/always.png                                             |
|    :width: 15.92cm                                                      |
|    :height: 6.46cm                                                      |
|    :align: center                                                       |
+=========================================================================+
| Figure 1.10. The property *always p*  is also known as *invariance      |
| property* or simply *invariant*.                                        |
+-------------------------------------------------------------------------+

**Eventually property**
This property evaluates to true if the expression *p* holds at some time
in the future.

+-------------------------------------------------------------------------+
| .. image:: media/eventually.png                                         |
|    :width: 15.92cm                                                      |
|    :height: 6.46cm                                                      |
|    :align: center                                                       |
+=========================================================================+
| Figure 1.10. The property *eventually p* can be used to check for       |
| progress during proof evaluation.                                       |
+-------------------------------------------------------------------------+

**Until property**
The property *p until q* is true starting from an initial point if *q*
is true in some reachable state from the initial state, and *p* is true
in all states until *q* is asserted.

+-------------------------------------------------------------------------+
| .. image:: media/until.png                                              |
|    :width: 15.92cm                                                      |
|    :height: 6.46cm                                                      |
|    :align: center                                                       |
+=========================================================================+
| Figure 1.10. The property *eventually p* can be used to check for       |
| progress during proof evaluation.                                       |
+-------------------------------------------------------------------------+


Safety Properties
-----------------
A safety property, in short, checks that something bad never happens. It
is the most used type of property in FPV because it is less complicated for
a solver to find a proof, compared to the *liveness* case (for example,
by proving inductively that the property is an invariant).

These might be the results of a safety property:

* A full proof is reached, meaning that the solver can guarantee that
  a "bad thing" can never happen.
* A bounded proof showing that the "bad thing" cannot happen in a certain
  number of cycles.
* A counterexample of finite prefix showing the path where the "bad thing"
  happens.

An example of a safety property extracted from IHI0051A amba4 axi4 stream
is shown below:

+----------------------------------------------------------------------+
| .. literalinclude:: ./child/tvalid_tready.sv                         |
|     :language: systemverilog                                         |
|     :lines: 1-14                                                     |
+======================================================================+
| Figure 1.11. A safety property to state that a packet should not be  |
| dropped if the receiver cannot process it.                           |
+----------------------------------------------------------------------+

Liveness Properties
-------------------
A liveness property checks that something good eventually happens. This
kind of properties are more complex to check in FPV because, in contrast
with safety properties where CEX can be found in a single state,
for liveness properties this is not the case, since to find a CEX,
sufficient evidence is needed that the "good thing" could be postponed forever,
and sometimes an auxiliary property is needed to help the solver understand that
there is some progress ongoing (fairness assumption).

A safety property can be trivially proven by doing nothing, because this
will never lead to a scenario where a "bad thing" occurs. A liveness property
can point out that a system is not making any progress w.r.t the functionality
and time-lapse of the data that the design is supposed to provide.

An example of a liveness property is from the classic arbiter problem that
states that *every request must be eventually granted*, that can be described
in SVA as follows:

.. code-block:: systemverilog

    property liveness_obligation_arbiter;
      req |=> s_eventually gnt
    endproperty

Another example of a liveness property that defines that a handshake must
eventually occur between a sender and a receiver, from the IHI0022E AMBA
and AXI protocol spec, is shown below.

+----------------------------------------------------------------------+
| .. literalinclude:: ./child/deadlock.sv                              |
|     :language: systemverilog                                         |
|     :lines: 16-29                                                    |
+======================================================================+
| Figure 1.12. Using a liveness property to check for deadlock         |
| conditions. This is a very common practice.                          |
+----------------------------------------------------------------------+

A deep explanation of how a solver of a FPV tool finds a liveness CEX is
outside of the scope of this application note, but for the sake of clarity,
consider the Figure 1.13.

+-------------------------------------------------------------------------+
| .. image:: media/liveness.png                                           |
|    :width: 15.92cm                                                      |
|    :height: 4.2cm                                                       |
|    :align: center                                                       |
+=========================================================================+
| Figure 1.13. A very simplistic example of liveness resolution.          |
+-------------------------------------------------------------------------+


Verification Layer
------------------
A property by himself does not execute any check unless is instantiated with
a verification statement. A property can be used with the following verification
directives:

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

----------------------------
More Advanced SVA Constructs
----------------------------

Checkers
--------

SVA IP
------


.. note::
   For simulation, properties works as monitors that checks the traffic/behavior
   of the test vectors applied to the design under test. For FPV, properties are
   non-deterministic since all possible values are used to check a proof.


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

.. [5]
   These restrictions are described in P1800 Section 16.6 Boolean expressions.

.. [6]
   Sequential Extended Regular Expressions.