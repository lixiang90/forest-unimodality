import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell202
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-17301156198548647735435679/10000000000000000000000000)
  B := (5200050439324945678043477/50000000000000000000000000)
  C := (45723546827343905518681311/10000000000000000000000000000)
  dδ := (12333744931193438287841957/200000000000000000000000000)
  dM := (2778238129559083336751757/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2723128499310106587216751/250000000000000000000000), (31612410881557084785242751/10000000000000000000000000), (72159042924775164351558487/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (12116/22791)
  hi := (24257/45582)
  vmin := (517280525/2077718724)
  damping := (517280525/2077718724)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell202
