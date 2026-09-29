import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell173
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (139)
  A := (-3695308412636627661811417 / 2000000000000000000000000)
  B := (15900115637833647785903679 / 200000000000000000000000000)
  C := (5571465042500793087010269 / 2500000000000000000000000000)
  dδ := (46073144027198247030252531 / 1000000000000000000000000000)
  dM := (61867091861689726874778961 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(15113802345526397008512731 / 10000000000000000000000000), (91074537775129073224889 / 4000000000000000000000), (5641424827866827484967871 / 50000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 207)
  hi := (27 / 52)
  vmin := (675 / 2704)
  damping := (675 / 2704)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell173
