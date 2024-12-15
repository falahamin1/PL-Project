# Exploring Theorem Proving with Lean 4: A Journey Through Software Foundations Vol. 1

## Introduction to Software Foundations Vol. 1

*Software Foundations* Vol. 1 is a widely-used resource for learning the fundamentals of theorem proving and functional programming. Written with Coq as the primary language, this book offers a structured approach to understanding logic, proofs, and functional programming concepts. The book is designed to give readers a strong foundation in formal reasoning and verification.

Our project aims to bridge the gap between *Software Foundations* and Lean 4, a newer theorem prover. Specifically, we’ve implemented examples (but not exercises) from multiple chapters of *Software Foundations Vol. 1* in Lean 4. This implementation provides a valuable resource for those looking to learn theorem proving in Lean 4 while referencing the detailed explanations in the book. Readers can benefit from studying the concepts in Coq and seeing how they translate into Lean 4, making it a practical guide for learners.

## Lean 4 and How It Compares to Coq

Lean 4, like Coq, is a powerful proof assistant and programming language designed for writing formal proofs and verified software. While Coq has been a long-standing favorite for theorem proving, Lean 4 offers several advantages:

- **Modern Syntax and Features**: Lean 4 boasts a clean and modern syntax with native support for metaprogramming, which makes writing and automating proofs more intuitive.
- **Performance**: Lean 4 introduces a more performant runtime, making it suitable for larger and more complex projects.
- **Interactivity**: Lean 4 has excellent tooling and integration with modern editors like VS Code, enhancing the interactive proof development experience.

That said, Coq still has a broader user base and a more extensive library ecosystem due to its long history. By implementing *Software Foundations* examples in Lean 4, our work allows users to compare the two systems and gain insights into their respective strengths.

## Chapters Implemented

Below is a list of chapters from *Software Foundations Vol. 1* that have been implemented in Lean 4, along with links to the table of contents for the book. 

The full table of contents can be found [here](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html).

### Basics
Most of the implemented examples from this chapter have been translated into Lean 4. 

### Induction
Examples from this chapter, except for the sections on `Nat` and `Bin`, have been implemented in Lean 4.

### Lists
Most examples from the chapter have been implemented, except for the section on Options.

### Polymorphism
We have implemented most of the examples, except for the section on Church numerals.

### Tactics
We’ve provided analogues to the Coq tactics mentioned in this chapter, along with their examples. For additional details on Lean 4 tactics, you can refer to [Lean 4 Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html).

### Logic
Most of the examples from this chapter have been implemented.

### Inductively Defined Propositions
Most examples from this chapter have been implemented, except for additional exercises and some parts of regular expressions.

### Maps
Most examples from this chapter have been implemented.

### Imperative Programs
We have implemented most of the examples from this chapter, except for the reasoning part.

## How You Can Extend This Work

Our implementation provides a starting point for exploring theorem proving in Lean 4 using *Software Foundations* as a guide. You can extend this work in several ways:

1. **Complete the Missing Sections**: Implement the chapters and sections that were omitted.
2. **Add New Examples**: Extend the examples with additional use cases and problem domains.
3. **Create Tutorials**: Develop step-by-step tutorials for learners to bridge the gap between *Software Foundations* and Lean 4.
4. **Explore Advanced Features**: Experiment with Lean 4’s metaprogramming capabilities to automate some of the proofs.

## Access the Repository

You can find the GitHub repository for this project [here](https://github.com/falahamin1/PL-Project). It contains all the implemented examples, organized by chapter. Contributions are welcome!

## Conclusion

This project aims to make theorem proving in Lean 4 more accessible by leveraging the excellent resources provided by *Software Foundations Vol. 1*. Whether you’re a student, researcher, or hobbyist, we hope this work inspires you to dive deeper into the world of formal verification and theorem proving.
