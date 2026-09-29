import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (26120832095767860693058537/100000000000000000000000000)
  B := (31152089004317182890924087/500000000000000000000000000)
  C := (38764207695259327718373399/5000000000000000000000000000)
  dδ := (11996909148015270918374853/100000000000000000000000000)
  dM := (1930341717092565905801449/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7552527090775495999253053/1000000000000000000000000), (2140017446247026455807827/100000000000000000000000), (10196300517770817251061999/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7977/15052)
  hi := (95749/180624)
  vmin := (8126696375/32625029376)
  damping := (8126696375/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell162
