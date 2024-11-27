# Formal security proofs and post-processing for quantum key distribution

**This is a work in progress! Contributions of any kind very welcome!**

# Background

## Quantum key distribution

[Quantum key Distribution](https://en.wikipedia.org/wiki/Quantum_key_distribution) (QKD) enables the exchange of a secret cryptographic key between authenticated parties by taking advantage of quantum effects.
It is rapidly evolving as an academic field, as well as approaching technological maturity, with several companies offering products based on QKD (see, e.g. [Pirandola et al.](http://arxiv.org/abs/1906.01645)).

Assuming the laws of quantum mechanics, the information-theoretic security of many QKD protocols can be rigorously proven.
However, in order for QKD systems to be truly useful, the standards of rigor in their implementation and evaluation must be very high.
This includes careful characterization of the physical devices, the software controlling them, and the protocol together with its theoretical background.
Crucially, this requires careful consideration and design of the *interplay* between these things.
This, in turn, requires massive collaboration between experts in experimental quantum optics, quantum information theory, and ("classical") information- and network security.

Formal verification can help provide the missing links between theoretical descriptions of QKD protocols, security proofs, and the software controlling a QKD device.
Furthermore, formal verification can provide the required strong assurances at a high level of rigor.

## Formal verification

[Formal verification](https://en.wikipedia.org/wiki/Formal_verification) is a set of tools and methods to help ensure correctness of mathematical proofs, as well as software.
In this project, we use the [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant) and programming language [Lean](https://en.wikipedia.org/wiki/Lean_(proof_assistant)) to make first steps towards the overarching goal of
- Formally and completely specifying quantum key distribution protocols, their security properties and assumptions (usually scattered across numerous scientific publications)
- Writing software that could control a QKD system, analyze measurement results and handle classical communication between QKD systems
- Writing a computer-verified proof that the software conforms to the protocol and satisfies the assumptions (e.g., how measurement results must be analyzed and what data must be sent via the classical communication).

While this project is unlikely to completely achieve this goal (without major collaboration and help from others), proof assistants enable reuse of definitions and theorems in other definitions and proofs while still ensuring that the entirety of every proof is checked by the computer.
Thus, everything done here can be reused in other Lean projects and the effort in formulating the definitions and abstractions also makes it unambiguous and much easier to translate and use in another proof assistant or any programming language.
It also enables collaboration between researchers by making it much easier to ensure consistency between different definitions and different results applied to similar problems.

Writing down all these details in a proof assistant requires deep understanding of the material and explicitly spelling out all details in full.
This is a large effort for most formalization projects.
However, Lean's fast-growing general Mathematics library ([Mathlib](https://github.com/leanprover-community/mathlib4)) makes this much easier compared to even a few years ago.
Furthermore, progress in AI is making it much easier to write proofs of theorems stated by a human user, while still ensuring that the proof is fully checked by the proof assistant's kernel (a small and heavily scrutinized piece of software which does not use AI and is thus extremely unlikely to approve an incorrect proof).

The crucial task then becomes making correct definitions correctly understanding the meaning of what has been proved, such that they are actually relevant to the practical problems one is solving.

# This software

## Verified secret key length computation

This software contains equations from [Rusca et al.](http://aip.scitation.org/doi/10.1063/1.5023340) (more comprehensive in [Wiesemann et al.](https://doi.org/10.48550/arXiv.2405.16578)) written out in two ways:

- **Using real-number computations. ("non-computable form")** This allows formally proving theorems about the equations without worrying about floating point arithmetic.
  However, due to the intricacies of supporting arbitrary real numbers, it is not possible to use these equations to compute quantities from given inputs.
- **Using interval arithmetic with floating point numbers. ("computable form")** This allows computing quantities given inputs.
  However, formally proving theorems about this form of the equations is extremely cumbersome.
  The subject of such proofs is "numerics", as opposed to the equations, whose subject is "quantum information theory".

**The non-computable form** might serve a quantum information theorist interested in formal proof as a dependency.
They could formalize the definitions of the theoretical framework in which the equations are relevant (composable security of quantum key distribution) and then formally prove that the equations as written out here are derived from that framework under certain modelling assumptions.
This repository does not (yet) include these formalized definitions and proofs, since it requires knowledge scattered across many publications and would be a huge undertaking without close collaboration with theory experts.
**If you're a theorist interested in this research direction, feel free to reach out!**

**The computable form** might serve as a dependency for an implementer of a quantum key distribution system who is interested in formal verification as a means of improving the quality and security of their software and thus their entire device.

The inputs and outputs of the equations are all rational numbers with real numbers only used in intermediate computations.
**This allows linking the computable and non-computable forms**.
We formally prove that the result of the computable form never exceeds the result of the real-number computation.
Thus, the needs of both theorists and implementors of QKD device software may be satisfied while assuring the compatibility between any work based on either of these formulations.
This alleviates the need for separate specifications, aligning definitions and bug-hunting, without requiring (in principle) any communication between the two audiences.

Thus, this repository tries to contribute a small but indispensable piece of a full formal framework for quantum key distribution and its post-processing, bridging the gap from theory to applications while avoiding leaky abstractions along the way, at least on the software level.

### Example usage

Set up a Lean environment (see [official Manual: "Quickstart" ](https://lean-lang.org/lean4/doc/quickstart.html)).
This should also download and install [Elan (lean version manager)](https://github.com/leanprover/elan) and Lean.

To build the executable, run
```sh
> lake build
```

This should give you an executable file, which can be run thus:
```sh
> .lake/build/bin/formalqkd
Enter
n_Z_μ1 n_Z_μ2 n_X_μ1 n_X_μ2 m_Z_μ1 m_Z_μ2 m_X_μ1 m_X_μ2
# Now enter some numbers. E.g.,
8875913 1124087 165048 20902 185856 26055 3456 484
Enter λ_EC
# Again enter number, E.g.,
1776924
# We get the result, computed by the executable, and partially verified correctness w.r.t. real-number valued specification given in `FormalQKD/RuscaEqn.lean`.
Computed: SKL = 1464719
```

## Sifting
*This is work in progress with only minimal progress at the moment.*

This repository also contains a partial implementation of basis sifting (part of QKD post-processing) with the goal of verifying formal properties about the executable code.


### Example usage

No examples at the moment, just look at `FormalQKD/Sifting.lean`.


## Acknowledgements

Many thanks to Geoffrey Irving for invaluable help with using their interval arithmetic library, as well as for making and accepting modifications that enable this use-case.

Many thanks to TODO for helpful discussions.

Finally, many thanks to the [Mathlib community](https://leanprover.zulipchat.com/) for their patient help with learning to use Lean, the library and also accepting my contributions to it, which are used in this repository.

## Dependencies

- `mathlib4` (https://github.com/leanprover-community/mathlib4). The Lean4 mathematics library.

- `interval` (https://github.com/girving/interval) by Geoffrey Irving. A Lean library for formally verified interval arithmetic.
