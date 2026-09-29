import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell174
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (171)
  A := (-15385532146397080011013259 / 10000000000000000000000000)
  B := (30173377254555155957405077 / 500000000000000000000000000)
  C := (1174157553157085241181401 / 625000000000000000000000000)
  dδ := (39454265527523131595888373 / 1000000000000000000000000000)
  dM := (2033141453190931966822641 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(13550257416090211393111531 / 1000000000000000000000000), (1948420296947845287149903 / 12500000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell174
