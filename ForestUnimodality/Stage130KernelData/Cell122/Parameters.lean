import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 89
  A := (-15810855065673596231334841/10000000000000000000000000)
  B := (49030685442515195560098107/500000000000000000000000000)
  C := (6777270017087105337394437/2000000000000000000000000000)
  dδ := (61787230841655382818089493/1000000000000000000000000000)
  dM := (2626330386307633739037537/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3220917820573056200572637/250000000000000000000000), (3981102479500416180258071/250000000000000000000000), (7319055587163513010295901/125000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11/21)
  hi := (1549/2954)
  vmin := (2176345/8726116)
  damping := (2176345/8726116)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell122
