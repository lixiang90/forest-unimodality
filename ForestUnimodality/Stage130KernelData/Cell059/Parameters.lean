import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 80
  A := (-1158764821549816904635577/1000000000000000000000000)
  B := (11028511454387733559112661/125000000000000000000000000)
  C := (-10802688537768390542731511/10000000000000000000000000000)
  dδ := (68688788589421428953940563/1000000000000000000000000000)
  dM := (321847455774432379292313/312500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5204773688555592414672901/500000000000000000000000), (21643070210699896449568769/1000000000000000000000000), (46721019070903409442507837/1000000000000000000000000)]
  retention := ![(7/10), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4777/9702)
  hi := (3193/6468)
  vmin := (23526725/94128804)
  damping := (23526725/94128804)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell059
