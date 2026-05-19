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
* `Split`: first-bad-collider extraction interface, imported through `Assembly`.
* `Assembly`: final reverse-direction assembly.

Phase 4 is actively being proved.  Do not treat `TraceSynthesis/Split.lean` as a
stable closed proof while `exists_split` is under construction.
-/
