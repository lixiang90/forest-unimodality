import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 125
  A := (2678613401450668152392609/20000000000000000000000000)
  B := (9536025323309388346260107/100000000000000000000000000)
  C := (3552931445031137780432573/5000000000000000000000000)
  dδ := (609770283023809867017917/4000000000000000000000000)
  dM := (8307882680592603916180927/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(36258215815862970821115141/5000000000000000000000000), (9594180796874041128319277/2500000000000000000000000), (14290677203104916515030709/500000000000000000000000), (18614901450033126906191683/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94453/178928)
  hi := (47239/89464)
  vmin := (1994666775/8003807296)
  damping := (1994666775/8003807296)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell130
