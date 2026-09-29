import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 15
  A := (36927503002903548932067679/1000000000000000000000000000)
  B := (28394319074653368017990829/1000000000000000000000000000)
  C := (-34341256972918912659942237/1000000000000000000000000000)
  dδ := (1066974666536394944493793/40000000000000000000000000)
  dM := (13541228483210590994960387/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(19701037968261450039619831/5000000000000000000000000)]
  retention := ![(1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/35)
  hi := (37/140)
  vmin := (234/1225)
  damping := (374400000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell001
