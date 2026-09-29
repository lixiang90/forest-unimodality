import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell426
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (21)
  A := (11207628035687624974414689 / 125000000000000000000000000)
  B := (18316157171818982229982709 / 1000000000000000000000000000)
  C := (27905428671219027758620967 / 1000000000000000000000000000)
  dδ := (8221250193992833341094517 / 500000000000000000000000000)
  dM := (7198654192192358025614851 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(32263631971016066835034053 / 5000000000000000000000000), (32336593179231254424621511 / 100000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 78)
  hi := (107 / 156)
  vmin := (5243 / 24336)
  damping := (13107500000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell426
