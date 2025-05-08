Building Blocks: An Examination of the Graphical Properties of Software Architecture
is a Logic for Systems project that examines properties of software architecture
through a graph grammar. The project is heavily inspired by

## Project name

Building Blocks: An Examination of the Graphical Properties of Software Architecture

### Inspiration

We have drawn heavy inspiration from and based our models off of the research
paper, A Graph Grammar Approach to Software Architecture Verification and
Transformation.

https://static.aminer.org/pdf/PDF/000/112/260/a_graph_grammar_approach_to_software_architecture_verification_and_transformation.pdf

### Collaborators

ajacks41, ksam2, rmani1

### Online Resources

OpenAI. (2025) ChatGPT (**\_ ** Version)[Large Language Model] https://chat.openai.com/chat

### Time

~25-30 hours per person.

### GitHub Repo

https://github.com/alejack312/stack-modeling/tree/main

## Design choices

**High-Level Design**
Our project models software architecture styles and design patterns using Relational  
Forge language. The codebase is organized around architectural styles
(client-server, distributed, pipe-and-filter), inheritance and interface
relationships, design patterns (composite, decorator), association/aggregation/composition
relationships, and root and hierarchy structures.

Each architectural or design concept is represented as a set of signatures
(sigs) and predicates that capture the structural and behavioral constraints of
the style or pattern.

**Relationships between Sigs and Predicates**

- Sigs represent the core entities in the architecture, such as `Class`,
  `Interface`, `Client`, `Server`, `Data`, `Task`, `Str`, `Composite`, and `Decorator`.
- Predicates encode the rules and constraints that define valid instances of these entities and their relationships. For example
  `inheritanceConstraints` enforces valid inheritance hierarchies, `pipeFilterStructure` defines valid pipe-and-filter graphs, and `compositeStructure` encodes the composite design pattern.
- Transformation predicates (e.g., `transform`, `transformPF`) model architectural rewrites, such as converting a client-server
  architecture to a distributed one or adding feedback to a pipe-and-filter system.

**Data Structures and Modeling Choices**

- We use sets and relations in sigs to model associations (e.g., `childrenC: set Component` in `Composite`, `ds: set Data` in `Client`).
- Abstract sigs and inheritance are used to capture generalization (e.g., `abstract sig Server {}`, `one sig Ctrl extends Server {}`).
- Functional and partial functional relations (e.g., `parentOrder: pfunc Class -> Int`) are used to model ordering and policies in inheritance.
- The use of `one`, `set`, and `lone` multiplicities allows us to precisely control the allowed cardinalities in the model.
- Predicates are composed modularly, so that constraints can be reused and combined for different runs and tests.

## Notes and Design Choices from the Codebase

Throughout the codebase, we have included several notes and design checks to clarify modeling decisions and highlight important considerations:

- **Interfaces and Implementers**: We chose to remove the implementer field from the Interface sig and instead let each Class sig have a set of interfaces it implements. This enables modeling multiple interface inheritance, as in Java, and avoids redundancy.

- **Redundant Inheritance**: We identified and addressed the problem of redundant inheritance, where a class could inherit from both a parent and a grandparent simultaneously. The `noRedundantInheritance` predicate ensures that a class cannot inherit from both a parent and its ancestor, maintaining a clean hierarchy.

- **Generalization Hierarchy**: The model enforces that inheritance relationships flow from general to specific, reflecting UML semantics. This is discussed in the comments for the `generalization` predicate.

- **Interface Multiplicity**: The model restricts each class to implement at most one interface (or none), as specified in the `interfaceMultiplicity` predicate. This is based on a production from the referenced research paper.

- **Resolution Policies for Multiple Inheritance**: We explored different resolution policies (LeftWins, RightWins, RequireOverride, MergeAll) for handling method and field conflicts in multiple inheritance scenarios. The `resolution` predicate encodes these policies, and comments explain the intended behavior for each.

- **RequireOverride Policy**: For this policy, if two parents share a method, the subclass must declare its own version. This is explicitly noted in the comments, and the model enforces that the subclass's methodsC set must include the conflicting method.

- **Data Structures**: The use of sets, relations, and multiplicities (one, set, lone) is intentional to precisely capture associations, generalizations, and constraints in the architecture.

- **Transformation Modeling**: The transformation predicates are designed to model architectural rewrites, and comments clarify the need for per-client data links and the preservation of client counts across transformations.

- **Testing and Modularity**: Predicates are composed modularly, and the codebase includes extensive test suites to ensure that each design choice and constraint is properly enforced and can be independently verified.

These notes and design checks are present as comments in the `.frg` files and serve both as documentation and as a guide for future extensions or modifications to the model.

## Errors/Bugs

**Reproduction Steps for Known Issues:**

- If a referenced field is not declared in a sig (e.g., using `dsB` in a predicate without declaring it in `BC`), Forge will report an "unbound identifier" error. To reproduce: remove or misspell a field in a sig and reference it in a predicate.
- If the transformation predicates are unsatisfiable (e.g., due to missing Data instances or incorrect modeling of per-client data links), running the corresponding `run` command will fail to produce an instance. To reproduce: run `runTransform` with insufficient Data or without modeling per-client data links in `BC`/`AC`.
- If the pipe-and-filter and client-server logic are not connected, removing one will not affect the other, but unsatisfiability may still occur due to unrelated modeling issues.

## Tests

**Testing Suites**

- The codebase includes extensive test suites (see `architecture.test.frg`, `inheritance.test.frg`, `design-pattern.test.frg`) that
  assert key properties of each architectural style, inheritance model, and design pattern.
- Each test suite uses `assert` statements to check that the model admits valid instances and rejects invalid ones (e.g., no
  self-inheritance, correct method resolution, valid composite/decorator structures).
- Example instances are provided to illustrate both valid and invalid configurations for design patterns.

**How to Run the Tests**

- Open the relevant `.frg` test file in the Forge IDE or compatible tool.
- Use the `run` or `assert` commands provided in the test suites to check the model. For example, run `runClientServerArchitecture` or
  the named test suites in the test files.
- The output will indicate whether the assertions are satisfiable (valid) or unsatisfiable (invalid), helping to verify the correctness
  of the model.

For more details on the structure and usage of the model, see the comments and documentation within each `.frg` file.


