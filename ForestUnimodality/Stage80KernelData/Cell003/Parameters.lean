import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 16
  A := (15340875244238388335205059/500000000000000000000000000)
  B := (47006490447402771160057/1600000000000000000000000)
  C := (-18038558068371256248862977/500000000000000000000000000)
  dδ := (26330993722685241964498459/1000000000000000000000000000)
  dM := (28944903916525453529615119/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(10430932429055468635414883/50000000000000000000000000), (263550490574424811640597/62500000000000000000000)]
  retention := ![(1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/70)
  hi := (39/140)
  vmin := (969/4900)
  damping := (387600000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell003
