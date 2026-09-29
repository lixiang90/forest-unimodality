import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 92
  A := (-2829470851811738498753357/2000000000000000000000000)
  B := (88528950891500479691842429/1000000000000000000000000000)
  C := (98513174494690720472273027/1000000000000000000000000000000)
  dδ := (7578915060358058265743697/125000000000000000000000000)
  dM := (92175282961345114500495423/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12316301000618087968518921/1000000000000000000000000), (78208440766167669266906159/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/2)
  hi := (405/808)
  vmin := (163215/652864)
  damping := (163215/652864)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell069
