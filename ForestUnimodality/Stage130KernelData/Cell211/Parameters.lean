import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell211
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 114
  A := (-18401327622605351719187183/10000000000000000000000000)
  B := (6629104725437405531973667/50000000000000000000000000)
  C := (5398997317703117110321287/12500000000000000000000000)
  dδ := (84303504447164986923546337/1000000000000000000000000000)
  dM := (15117517650100830393922191/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10456862278828229051441667/1000000000000000000000000), (23752051008231753193022939/100000000000000000000000000), (40220299196348669568124023/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57/107)
  hi := (29/54)
  vmin := (725/2916)
  damping := (725/2916)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell211
