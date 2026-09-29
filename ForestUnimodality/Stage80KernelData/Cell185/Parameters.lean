import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell185
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 82
  A := (-2736409815631628863457081/2000000000000000000000000)
  B := (9292141012770505081874717/50000000000000000000000000)
  C := (58864554938598934175075783/100000000000000000000000000)
  dδ := (14745099357928423411401297/100000000000000000000000000)
  dM := (1669664016478875729829201/500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(89200569710064425699158619/100000000000000000000000000), (46315331958438372694786267/5000000000000000000000000), (12808659981057051169273109/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2557/4752)
  hi := (427/792)
  vmin := (155855/627264)
  damping := (155855/627264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell185
