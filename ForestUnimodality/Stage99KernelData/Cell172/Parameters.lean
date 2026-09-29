import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell172
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 36
  A := (11095333089260415498955581/5000000000000000000000000)
  B := (-26162053790813672576875959/1000000000000000000000000000)
  C := (17475936257431959330865823/100000000000000000000000000)
  dδ := (57569242537934876835503673/1000000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(33133298971939693089439061/10000000000000000000000000), (10407327431092594505201987/12500000000000000000000000), (15950059925205054001118299/50000000000000000000000000), (1232183072255428690766621/100000000000000000000000)]
  retention := ![(9/10), (7/10), (3/5), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/90)
  hi := (107/180)
  vmin := (7811/32400)
  damping := (7811/32400)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell172
