import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell175
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (211)
  A := (-17036605141335507307331909 / 10000000000000000000000000)
  B := (1115859229424116111362153 / 20000000000000000000000000)
  C := (3116712965743728257911327 / 2000000000000000000000000000)
  dδ := (3388827724891200349199849 / 100000000000000000000000000)
  dM := (16244373089449986040551377 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(2654205363566846553879941 / 125000000000000000000000), (18803037665656566446159559 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell175
