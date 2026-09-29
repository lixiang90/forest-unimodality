import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell231
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 33
  A := (-425940580398743080792201/1250000000000000000000000)
  B := (54498110068027509622634597/1000000000000000000000000000)
  C := (18608843475255379407151679/200000000000000000000000000)
  dδ := (33289785146630612722162823/1000000000000000000000000000)
  dM := (15744643727906278227873793/25000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(4963326907574509005982577/1250000000000000000000000), (20944489969203976542644341/2500000000000000000000000)]
  retention := ![(3/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (63/103)
  hi := (129/209)
  vmin := (10320/43681)
  damping := (10320/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell231
