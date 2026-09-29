import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell449
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (53)
  A := (-211934781123307507455511 / 1562500000000000000000000)
  B := (8251574613097664018246391 / 250000000000000000000000000)
  C := (-1056303604751828578711681 / 10000000000000000000000000)
  dδ := (28067484777605521822918533 / 1000000000000000000000000000)
  dM := (13499998951880414800597041 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(17020487024974761958162617 / 5000000000000000000000000), (578015972824653556649821 / 31250000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 17)
  hi := (64 / 153)
  vmin := (70 / 289)
  damping := (70 / 289)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell449
