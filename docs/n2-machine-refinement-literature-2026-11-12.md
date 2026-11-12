# N2 machine refinement scope check

The target is a universal induction over the recorded N2 update projection
with an explicit frame and refusal observation. The simulation approach
follows Leroy's semantic preservation proof, where a relation connects
source and target states. CompCert's theorem applies to its own compiler
and languages. It supplies no result about the Mojo compiler.
[Formal verification of a realistic compiler](https://xavierleroy.org/publi/compcert-CACM.pdf)

Goel's x86isa formalizes fetch, decode and execution against an independent
ISA model. That is the standard for discharging the ISA boundary here.
The current slice decoder and its projections are internal to PSC.
[ACL2 x86isa](https://acl2.org/doc/index-seo.php?xkey=X86ISA____INTRODUCTION)

The System V AMD64 ABI distinguishes saved registers from volatile
registers and gives stack alignment rules. It does not specify the
compiler's private result record or the behavior of its allocator and
stack-trace runtime. Those contracts need separate evidence.
[System V AMD64 ABI, §3.2](https://refspecs.linuxfoundation.org/elf/x86_64-SysV-psABI.pdf)

Proceed with the projected trace and explicit frame obligations. A stale
saved output base, overlapping counter and stack storage, or a rejecting
step that permits a later store invalidates the proposed composition.
