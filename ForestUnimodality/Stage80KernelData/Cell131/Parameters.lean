import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 33
  A := (88029840165212831394114801/100000000000000000000000000)
  B := (50579587779846918449422333/1000000000000000000000000000)
  C := (83923247995302974883147229/10000000000000000000000000000)
  dδ := (654275177803537610898843/4000000000000000000000000)
  dM := (10203181318227461712305759/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(69074029149021152207410523/10000000000000000000000000), (16481321290361556464176829/1000000000000000000000000), (2067281545350821758688653/200000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1549/2954)
  hi := (2326/4431)
  vmin := (4896230/19633761)
  damping := (4896230/19633761)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell131
