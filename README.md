#### Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

The goal of my project was to model technology stacks for software projects. Each stack includes various components (frontend, backend, database, ORM, authentication) along with relevant quality attributes like Speed, Security, and Reliability. In theory, by modeling these relationships, we can analyze tradeoffs and detect potential technological conflicts or limitations.

#### Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

The model is split into signatures for each component type (i.e. Frontend, Backend, Database) and predicates that capture how they interact or conflict. The default 
Sterling visualizer displays each generated stack. The associated technologies and qualities have been assigned. I attempted to create a custom visualization, 
however, I ran into issues getting it to work. The default visualization is 
still useful and satisfactory for understanding the model. 

#### Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

abstract sig Component - Represents a generic software component (e.g., Frontend, Backend, Database).

abstract sig Frontend extends Component - Represents a frontend technology (e.g., Next.js, React).

abstract sig Backend extends Component - Represents a backend technology (e.g., Node.js, Python).

abstract sig Database extends Component - Represents a database technology (e.g., Postgres, MongoDB).

abstract sig ORM extends Component - Represents an Object-Relational Mapping technology (e.g., Prisma, Drizzle).

abstract sig Authorization extends Component - Represents an authentication technology (e.g., OAuth, JWT).

##### Frontends
one sig NextJS extends Frontend - Represents a Next.js frontend.

one sig ReactJS extends Frontend - Represents a React.js frontend.

one sig Vite extends Frontend - Represents a Vite frontend.

one sig Angular extends Frontend - Represents a Angular frontend.

one sig SvelteKit extends Frontend - Represents a SvelteKit frontend.

one sig VueJS extends Frontend - Represents a Vue.js frontend.

##### Backends
one sig PythonBackend extends Backend - Represents a Python backend.

one sig NodeBackend extends Backend - Represents a Node.js backend.

one sig JavaBackend extends Backend - Represents a Java backend.

one sig GoBackend extends Backend - Represents a Go backend.

one sig RubyBackend extends Backend - Represents a Ruby backend.

##### Databases
one sig Postgres extends Database - Represents a Postgres database.

one sig SQLDatabase extends Database - Represents a SQL database.

one sig MongoDB extends Database - Represents a MongoDB database.

one sig Redis extends Database - Represents a Redis database.

one sig Firebase extends Database - Represents a Firebase database.

##### ORMs
one sig PrismaORM extends ORM - Represents a Prisma ORM.

one sig DrizzleORM extends ORM - Represents a Drizzle ORM.

##### Authorizations
one sig OAuth extends Authorization - Represents an OAuth authentication.

one sig JWTAuth extends Authorization - Represents a JWT authentication.

one sig FirebaseAuth extends Authorization - Represents a Firebase authentication.

one sig Auth0 extends Authorization - Represents an Auth0 authentication.

one sig ClerkAuth extends Authorization - Represents a Clerk authentication.


##### Quality Attributes
abstract sig Quality - Represents a quality attribute for a component.

one sig 
  Scalability, 
  Speed, 
  Reliability, 
  Maintainability, 
  Security, 
  DevExperience, 
  CostEfficiency, 
  Pedagogy 
extends Quality - Represents a quality attribute for a component.
=================================================================

Comprehensive Technology Stack definition
sig TechnologyStack {
    // Components
    frontend: one Frontend,
    backend: one Backend,
    database: one Database,
    orm: one ORM,
    auth: lone Authorization,  // Authentication is optional
    
    // Quality attributes for each pairing
    frontendBackendQualities: set Quality,
    backendDatabaseQualities: set Quality,
    databaseORMQualities: set Quality,
    authQualities: set Quality,
    
    // Overall qualities of the stack
    overallQualities: set Quality
} - Represents a technology stack with a frontend, backend, database, ORM, and optional authentication. Each component pairing has associated quality attributes. Overall,
the stack has a set of quality attributes that is the union of all component pairings.


The predicates in main.frg set the constraints for the model. 

exampleStack - An example stack with a Next.js frontend, Node.js backend, Postgres database, Prisma ORM, and OAuth authentication. The stack has Speed, Scalability, and Security qualities.

allQualitiesImpossible - No stack can optimize for all quality attributes.

validStacks - A stack is valid if it has a frontend, backend, database, ORM, and optional authentication.

technologyQualityImplications - Certain technologies inherently provide certain quality attributes. For example, Next.js provides Speed and Developer Experience.

qualityTradeoffs - Certain quality attributes are mutually exclusive. For example, a stack can't have both Speed and Reliability.

qualityBudget - Each stack can have a maximum of 6 quality attributes.

qualityPropagation - A stack's overall quality is the union of its component pairings.

technologyConflicts - Certain technologies conflict with each other. For example, Vite is not paired with Postgres. 

optimizedFor - Models a stack that is optimized for the given qualities.

microservicesArchitecture - Models a stack that is optimized for a microservices architecture.
 
rapidPrototyping - Models a stack that is optimized for rapid prototyping.

enterpriseArchitecture - Models a stack that is optimized for an enterprise architecture.

ecommerceStack - Models a stack that is optimized for an ecommerce application.
    
contentStack - Models a stack that is optimized for a content management system. 

realtimeStack - Models a stack that is optimized for a realtime application.

evolutionPath - Models how two stacks evolve from one to the other.

##### Assumptions
- Assumption that users using Firebase are not using an ORM.
- Assumption that any stack with authentication must include security as a quality attribute
- Assumption that high speed compromises reliability
- Assumption that strong developer experience reduces maintainability
- Assumption pedagogical stacks can't optimize for both speed and scalability
- Assumption that security features impact performance
- Assumption that firebase inherently reduces overall security
- Assumption that Vite frontend won't be paired with Postgres database due to a pedagogical focus
- Assumption that Node/Go backends with Postgres can't optimize for both speed and reliability simultaneously
- Assumption that no stack can optimize for all quality attributes
- Assumption that there are a maximum of 6 quality attributes per stack
- Assumption that component pairings have quality limits (3 for most, 2 for auth)
- Assumption that specific technologies inherently provide certain qualities (e.g., NextJS provides Speed and DevExperience)
- Assumption that architectural patterns require specific technology combinations
- Assumption that every stack needs a frontend, backend, and database
- Assumption that every component pairing must have at least one quality attribute

#### Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

For a test suite, I wrote variety of assert statements that ensure that the model is working as intended. I wrote tests to ensure that each stack has the necessary components, that certain qualities and components must exist together, and that certain combinations are limited. The tests run automatically, and as with other projects, the tests
will find a counterexample if a constraint is violated or a contradictory configuration is found.

- Correctness tests (i.e. validStacks) ensure each stack has the necessary components.
- Constraint tests (i.e. ecommerceStack) verify that certain qualities and components must
exist together.

- Tradeoff tests (i.e. qualityTradeoffs) confirm that certain combinations (Speed vs Reliability) are limited.


# stack-modeling
