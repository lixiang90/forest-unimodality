import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (140)
  A := (-18894408333834175517296217 / 10000000000000000000000000)
  B := (79683854160802480848246887 / 1000000000000000000000000000)
  C := (9782686348368571204858063 / 12500000000000000000000000000)
  dδ := (2786426990309546873614277 / 62500000000000000000000000)
  dM := (15388347535217255851111573 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(14723856569216604128769177 / 500000000000000000000000), (2172381116224926529412187 / 20000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51 / 101)
  hi := (26 / 51)
  vmin := (650 / 2601)
  damping := (650 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell158
