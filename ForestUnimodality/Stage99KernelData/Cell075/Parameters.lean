import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 62
  A := (-18726594701248785246150419/20000000000000000000000000)
  B := (18085488522280460110813749/200000000000000000000000000)
  C := (8885820781534939415483021/5000000000000000000000000000)
  dδ := (764361844769601977978013/10000000000000000000000000)
  dM := (12398917289774013562875243/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10306748032845800544521353/1250000000000000000000000), (26371811409170131668133763/500000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3493/6868)
  hi := (26/51)
  vmin := (650/2601)
  damping := (650/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell075
