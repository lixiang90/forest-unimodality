import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 54
  A := (32513803749025824652463257/50000000000000000000000000)
  B := (35119034090662581970576639/1000000000000000000000000000)
  C := (-6651061368347478165719/2000000000000000000000000)
  dδ := (4452051573233199027734841/50000000000000000000000000)
  dM := (20553541102875615945340393/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(860011391233505007036797/156250000000000000000000), (9633180373433846144237691/2500000000000000000000000), (5650903190116514096530409/125000000000000000000000)]
  retention := ![(4/5), (9/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2983/6208)
  hi := (4487/9312)
  vmin := (9620175/38539264)
  damping := (9620175/38539264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell044
