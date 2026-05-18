import DSeparation.TraceSynthesis.Graph
import DSeparation.TraceSynthesis.StaticRoute
import DSeparation.TraceSynthesis.OpenTrace
import DSeparation.TraceSynthesis.MinimalWitness
import DSeparation.TraceSynthesis.Assembly

/-! # Trace Synthesis

Aggregating module for the reverse witness-synthesis pipeline:

* `Graph`: graph lemmas used by normalization.
* `StaticRoute`: explicit static IR for moral-graph reachability.
* `OpenTrace`: local-open trace compiler and active-route bridge.
* `MinimalWitness`: bad-collider minimality wrapper.
* `Assembly`: final reverse-direction assembly and remaining proof debt.
-/
