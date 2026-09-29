import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell233
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 29
  A := (-9961254114190761843161681/50000000000000000000000000)
  B := (44668877899846741452716259/1000000000000000000000000000)
  C := (38888041581577985350559601/500000000000000000000000000)
  dδ := (6028989578081145328525281/200000000000000000000000000)
  dM := (50005116312757465386884537/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10496575654323654636090879/12500000000000000000000000), (9942725476572014109422071/5000000000000000000000000), (15615977930834842979379573/2000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33/53)
  hi := (467/742)
  vmin := (128425/550564)
  damping := (128425/550564)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell233
