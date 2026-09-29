import ForestUnimodality.RowModel
import ForestUnimodality.TriangularLayers

/-! Real evaluation of executable integer rows on actual forest layer counts. -/
namespace ForestUnimodality
namespace FiniteRows
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def rowValue (G : SimpleGraph V) (S I : Finset V) (row : Row) : ℝ :=
  ∑ jm ∈ triangularIndices I.card (S \ I).card,
    (coeff S.card I.card row jm : ℝ) * (layerCount G I (S \ I) jm.1 jm.2 : ℝ)

def RowHolds (G : SimpleGraph V) (S I : Finset V) (row : Row) : Prop :=
  rowValue G S I row ≤ (rhs S.card I.card row : ℝ)

end FiniteRows
end ForestUnimodality
