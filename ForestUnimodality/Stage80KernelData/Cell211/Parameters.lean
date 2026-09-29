import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell211
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 41
  A := (-5588598828778302501874009/5000000000000000000000000)
  B := (2151329972799896281254739/12500000000000000000000000)
  C := (7966571627831381396944721/25000000000000000000000000)
  dδ := (1023426136505553862843243/10000000000000000000000000)
  dM := (8653932657734753845085729/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(14434006187365948647993719/1000000000000000000000000), (3323374340530215409472703/2000000000000000000000000)]
  retention := ![(3/10), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/93)
  hi := (107/187)
  vmin := (8560/34969)
  damping := (8560/34969)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell211
