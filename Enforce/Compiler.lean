import Enforce.Compiler.Clusters
import Enforce.Compiler.System

/-!
# The bounded-configuration compiler of V4 Part II

M2--M8, V4 2.10--2.17. This public entrypoint exports the compiler in all
Euclidean dimensions at least two, for the general expanding linear substitution.
All Euclidean isometries, including reflections, remain available.

`Clusters` contains the explicit geometric choices, finite tagged colours,
native projection, augmented point markings, and physical frame rigidity.
`System` contains the exact finite CORE/EVENT rule families and their decoration,
the disjointness facts, complete-cluster rigidity, honest lifts, and source languages.
It also supplies the actual certificate blocks and event configurations forced
in arbitrary proper outputs, including the uniform END coverage assertion.

The public data are `ClusterData`, `Colour`, `systemM`, `nativeDecoration`,
`honestLift`, `sourceLanguage`, and `KBlock`. The parser-facing conclusions are
`compiler_certificates`, `compiler_events`, `compiler_coverage`, and the bundled
`compiler_end_event`. No hierarchy or source-species membership is assumed on
an arbitrary proper output.

Definitions have genuine bodies. Substantial geometric and compiler proofs remain
explicit theorem obligations in this skeleton. `clusterData_exists` supplies the
finite geometric choices without assuming an honest source exists.
-/
