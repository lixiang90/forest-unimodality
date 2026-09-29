import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell209
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (145)
  A := (-7553251340900408400358401 / 5000000000000000000000000)
  B := (16539602290683918378588757 / 250000000000000000000000000)
  C := (25208908972141119697596423 / 100000000000000000000000000)
  dδ := (39452636465166592005804347 / 1000000000000000000000000000)
  dM := (4457357641273964493112969 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(52801414704839650937628903 / 10000000000000000000000000), (6366592928831653175336669 / 250000000000000000000000), (35208314165617174751332641 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57 / 107)
  hi := (29 / 54)
  vmin := (725 / 2916)
  damping := (725 / 2916)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell209
