import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell093.Parameters
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch000_049
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch050_099
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch000_049
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree000.table
  base := (38884209610480927766786862361/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1182628671856154195518584500000000000000)
      linear := (-24624776665326344494977295000000000000)
      constant := (388842096104809277667868623610000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree000.table
  base := (38884209610480927766786862361/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1182628671856154195518584500000000000000)
      linear := (-24624776665326344494977295000000000000)
      constant := (388842096104809277667868623610000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree001.table
  base := (220234428079581491823370818301697788906173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-32494786248127747213397205793659795000000000000)
      constant := (5851845561626935427400248337219675877687495880573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree001.table
  base := (219833174114828756056477625880929976830847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-3618992527970765037962350961461505000000000000)
      constant := (649026515998938893284454452204679729465274901383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12498154918677782967/25000000000000000000)
  directionHi := (49992619674711131869/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree002.table
  base := (25918755265488543477414466141090699685151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-64336208197324946928251733519566295000000000000)
      constant := (3471460105996898242806342993468978503484370689755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree002.table
  base := (16145555180407668706477609286769944310143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-7165389022727024798308848804283755000000000000)
      constant := (384469439918643142661410447411876619310761333816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/25000000000000000000)
  centralHi := (49992619674711131869/100000000000000000000)
  directionLo := (70700240762536509997/100000000000000000000)
  directionHi := (35350120381268254999/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree003.table
  base := (79805818934811957634612047850557311268413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-10686403349613571849234029027274755000000000000)
      constant := (243462963544298263340495665616175230719984412757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree003.table
  base := (39727334475384327938148922123943607699327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-10711785517483284558655346647106005000000000000)
      constant := (242466687590480814804861375358571525457402472206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70700240762536509997/100000000000000000000)
  centralHi := (35350120381268254999/50000000000000000000)
  directionLo := (4329487864003357981/5000000000000000000)
  directionHi := (86589757280067159621/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree004.table
  base := (1611791431792691477024216717306608793429/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-128019052095719346357960788971379295000000000000)
      constant := (1499061824857736167171438752338807657228856468128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree004.table
  base := (51314804787875980623814361200680482147469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-14258182012239544319001844489928255000000000000)
      constant := (165857608536585908242266167115087316933649736741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4329487864003357981/5000000000000000000)
  centralHi := (86589757280067159621/100000000000000000000)
  directionLo := (12498154918677782967/12500000000000000000)
  directionHi := (99985239349422263737/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree005.table
  base := (17430877218665109000403735911344039283549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-159860474044916546072815316697285795000000000000)
      constant := (1128582650981234356746822201530844986193176381498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree005.table
  base := (17335245369205039066201238377761246541729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-17804578506995804079348342332750505000000000000)
      constant := (124942098117798455048470495659610951111918611762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/12500000000000000000)
  centralHi := (99985239349422263737/100000000000000000000)
  directionLo := (22357379193189502981/20000000000000000000)
  directionHi := (55893447982973757453/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree006.table
  base := (2439850426715569252293726363396905719277/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-21300210666012638420852204935910255000000000000)
      constant := (104461187036804286693779668998201608850376116530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree006.table
  base := (12128954016451741394657012517806165344661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-21350975001752063839694840175572755000000000000)
      constant := (104201950121857883992653233400570287869552605658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22357379193189502981/20000000000000000000)
  centralHi := (55893447982973757453/50000000000000000000)
  directionLo := (30614102277016354781/25000000000000000000)
  directionHi := (979651272864523353/800000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree007.table
  base := (17423811955650086019065643625734247513219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-223543317943310945502524372149098795000000000000)
      constant := (860435538899466056104106893138373895652984596419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree007.table
  base := (17317343025313886703304246692257549182407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-24897371496508323600041338018395005000000000000)
      constant := (95501283105716973646022508994437963411613070223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30614102277016354781/25000000000000000000)
  centralHi := (979651272864523353/800000000000000000)
  directionLo := (132268039047920423511/100000000000000000000)
  directionHi := (16533504880990052939/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree008.table
  base := (12470941742710211410932059272208394206291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-255384739892508145217378899875005295000000000000)
      constant := (850520609643515182113833151678081014005072051091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree008.table
  base := (309676541535130984702399288311560019839/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-28443767991264583360387835861217255000000000000)
      constant := (94530774983157020166539946044115336693085506840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132268039047920423511/100000000000000000000)
  centralHi := (16533504880990052939/12500000000000000000)
  directionLo := (70700240762536509997/50000000000000000000)
  directionHi := (28280096305014603999/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree009.table
  base := (8750213978413998130845912259520492606369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-31914017982411704992470380844545755000000000000)
      constant := (98828164728694888265856013552228992027417778841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree009.table
  base := (4340719064871378827600928998986709990387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-31990164486020843120734333704039505000000000000)
      constant := (98974330941371065018841086262472506737700040886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70700240762536509997/50000000000000000000)
  centralHi := (28280096305014603999/20000000000000000000)
  directionLo := (37494464756033348901/25000000000000000000)
  directionHi := (29995571804826679121/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree010.table
  base := (5827237405690692855935418902008949037709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-319067583790902544647087955326818295000000000000)
      constant := (965708540863684352104874018967608020036674392909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree010.table
  base := (5768909291268637759205716581097537845863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-35536560980777102881080831546861755000000000000)
      constant := (107559664437297326616905660939964121750472405807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37494464756033348901/25000000000000000000)
  centralHi := (29995571804826679121/20000000000000000000)
  directionLo := (31618108874126640633/20000000000000000000)
  directionHi := (79045272185316601583/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree011.table
  base := (3455519642554756914045674369677968882219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-350909005740099744361942483052724795000000000000)
      constant := (1072745651240567972784252511642505039936109165419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree011.table
  base := (106400127602686517917886988761881923907/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-39082957475533362641427329389684005000000000000)
      constant := (119565463402380730934028128232018129513410039136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31618108874126640633/20000000000000000000)
  centralHi := (79045272185316601583/50000000000000000000)
  directionLo := (165806761747956045531/100000000000000000000)
  directionHi := (41451690436989011383/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree012.table
  base := (744584517155219137981546140675017404117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-42527825298810771564088556753181255000000000000)
      constant := (134077099938589083588263258449628752767771764826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree012.table
  base := (722172279353149522612442626021538832559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-42629353970289622401773827232506255000000000000)
      constant := (134564909563367233395362698560656609790680059502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165806761747956045531/100000000000000000000)
  centralHi := (41451690436989011383/25000000000000000000)
  directionLo := (173179514560134319241/100000000000000000000)
  directionHi := (86589757280067159621/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree013.table
  base := (-8141187921062277315017692162671526523/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-414591849638494143791651538504537795000000000000)
      constant := (1365138552793001684698953265196107307667980381540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree013.table
  base := (-202822923741851526695482260899764074691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-46175750465045882162120325075328505000000000000)
      constant := (152291632344314435731226683661497965428808284501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173179514560134319241/100000000000000000000)
  centralHi := (86589757280067159621/50000000000000000000)
  directionLo := (180250953631940847027/100000000000000000000)
  directionHi := (45062738407985211757/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree014.table
  base := (-780344811140589441066713102986293742399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-446433271587691343506506066230444295000000000000)
      constant := (1546481517148371627622313849953103829810764140802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree014.table
  base := (-319310895309795477951669959503527063851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-49722146959802141922466822918150755000000000000)
      constant := (172569170598406349246386395746935789509292846305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180250953631940847027/100000000000000000000)
  centralHi := (45062738407985211757/25000000000000000000)
  directionLo := (18705525469006318131/10000000000000000000)
  directionHi := (187055254690063181311/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree015.table
  base := (-2746724282637022074467874735659341736849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-53141632615209838135706732661816755000000000000)
      constant := (194400063161008977483316800319295174378354568439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree015.table
  base := (-694734106823919763681886825840216184181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-53268543454558401682813320760973005000000000000)
      constant := (195273450086252208961664606156622559139176079564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18705525469006318131/10000000000000000000)
  centralHi := (187055254690063181311/100000000000000000000)
  directionLo := (9681029171671873227/5000000000000000000)
  directionHi := (193620583433437464541/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree016.table
  base := (-469030529173729881653045497401050026581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-510116115486085742936215121682257295000000000000)
      constant := (1973664792394434550940702385747253099629452932952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree016.table
  base := (-3781169782650101178756715700424907732617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-56814939949314661443159818603795255000000000000)
      constant := (220312487463304730962897894778473614187456881087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9681029171671873227/5000000000000000000)
  centralHi := (193620583433437464541/100000000000000000000)
  directionLo := (12498154918677782967/6250000000000000000)
  directionHi := (199970478698844527473/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree017.table
  base := (-4601446908351337289306707772069561404759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (7161102)
      previous := (3580551)
      next := (3580551)
      square := (108575955734441660536365724360500000000000000)
      linear := (-1875285596661878694294358648471155000000000000)
      constant := (7674851776084415856744509397705388136990480969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree017.table
  base := (-4627387926789649706049393926387375557593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12063995081604628948485080484500000000000000)
      linear := (-208862755861837097589987254140545000000000000)
      constant := (856799776349957545804308632211937381936993807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/6250000000000000000)
  centralHi := (199970478698844527473/100000000000000000000)
  directionLo := (20612485142016560701/10000000000000000000)
  directionHi := (206124851420165607011/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree018.table
  base := (-5313628153639403804825804723615663816569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-63755439931608904707324908570452255000000000000)
      constant := (275798967587310352603009180078755836274674913359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree018.table
  base := (-5336849701909967124760891961309310270227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-63907732938827180963852814289439755000000000000)
      constant := (277124617010921498818043206305143249294756753797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20612485142016560701/10000000000000000000)
  centralHi := (206124851420165607011/100000000000000000000)
  directionLo := (26512590285951191249/12500000000000000000)
  directionHi := (212100722287609529993/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree019.table
  base := (-5904515628777616572765004091545317440297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-605640381333677342080778704859976795000000000000)
      constant := (2765723128526290674259310017895074227374770318103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree019.table
  base := (-5925259270129832018767804584778503729603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-67454129433583440724199312132262005000000000000)
      constant := (308794635133059447368129763138993458218298421333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512590285951191249/12500000000000000000)
  centralHi := (212100722287609529993/100000000000000000000)
  directionLo := (43582555416985808759/20000000000000000000)
  directionHi := (54478194271232260949/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree020.table
  base := (-255484645857411613805768627307689151081/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-637481803282874541795633232585883295000000000000)
      constant := (3068284316837689477974136792553005099612722302975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree020.table
  base := (-1601401556816191888613336420924391349461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-71000525928339700484545809975084255000000000000)
      constant := (342586895247013386511645342566175703123835479884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43582555416985808759/20000000000000000000)
  centralHi := (54478194271232260949/25000000000000000000)
  directionLo := (22357379193189502981/10000000000000000000)
  directionHi := (223573791931895029811/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree021.table
  base := (-6772287395519080241048584589063000457623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-74369247248007971278943084479087755000000000000)
      constant := (376620687591212155191249498655584140543886667553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree021.table
  base := (-6788733666493502597969270659277782814069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-74546922423095960244892307817906505000000000000)
      constant := (378469430949057130644305482157688400541454135859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22357379193189502981/10000000000000000000)
  centralHi := (223573791931895029811/100000000000000000000)
  directionLo := (28636870481062795661/12500000000000000000)
  directionHi := (229094963848502365289/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree022.table
  base := (-70691466841123026276932587192679921927/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-701164647181268941225342288037696295000000000000)
      constant := (3729386835254920105909273660292105862481537247300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree022.table
  base := (-7083745214068776623993923476922457946797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-78093318917852220005238805660728755000000000000)
      constant := (416415403938774867300945177530909695374085179067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28636870481062795661/12500000000000000000)
  centralHi := (229094963848502365289/100000000000000000000)
  directionLo := (58621542799280986809/25000000000000000000)
  directionHi := (234486171197123947237/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree023.table
  base := (-3642689061505029499094531576030555268843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-733006069130466140940196815763602795000000000000)
      constant := (4087482376657133225846708916968164161764574361514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree023.table
  base := (-3649155766421782435767552443446015382707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-81639715412608479765585303503551005000000000000)
      constant := (456402200419387031562173160379805037412821406154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58621542799280986809/25000000000000000000)
  centralHi := (234486171197123947237/100000000000000000000)
  directionLo := (239756181368963321239/100000000000000000000)
  directionHi := (5993904534224083031/2500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree024.table
  base := (-7427472673293943943161404411212498005687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-84983054564407037850561260387723255000000000000)
      constant := (495966732127652451388645653454348577966912217857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree024.table
  base := (-29755640801228542402159218333174005817/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-85186111907364739525931801346373255000000000000)
      constant := (498410723915950864052790569804064214591241571750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239756181368963321239/100000000000000000000)
  centralHi := (5993904534224083031/2500000000000000000)
  directionLo := (244912818216130838249/100000000000000000000)
  directionHi := (979651272864523353/400000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree025.table
  base := (-7500921100198810022681713377010265677721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-796688913028860540369905871215415795000000000000)
      constant := (4857895787348822554621863731323085708315898573479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree025.table
  base := (-7511018722893848303518352906769533041881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-88732508402120999286278299189195505000000000000)
      constant := (542424826251999800330882118540072339104094084591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244912818216130838249/100000000000000000000)
  centralHi := (979651272864523353/400000000000000000)
  directionLo := (12498154918677782967/5000000000000000000)
  directionHi := (249963098373555659341/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree026.table
  base := (-117349563901888680927131140424794701869/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-828530334978057740084760398941322295000000000000)
      constant := (5269944628596535554182472613217339264405151675584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree026.table
  base := (-187981819909953511443883927391288628527/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-92278904896877259046624797032017755000000000000)
      constant := (588430840983754913008477306119184174436578603880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/5000000000000000000)
  centralHi := (249963098373555659341/100000000000000000000)
  directionLo := (25491334325697464059/10000000000000000000)
  directionHi := (254913343256974640591/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree027.table
  base := (-3729881733073546531665451029091041605101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-95596861880806104422179436296358755000000000000)
      constant := (633304736820425820546874853209067237990918796022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree027.table
  base := (-7467597678270216808928184005048706805241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-95825301391633518806971294874840005000000000000)
      constant := (636417196102905085427096889766887785503243865551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25491334325697464059/10000000000000000000)
  centralHi := (254913343256974640591/100000000000000000000)
  directionLo := (129884635920100739431/50000000000000000000)
  directionHi := (259769271840201478863/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree028.table
  base := (-7352431969970184638941345179967675969791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-892213178876452139514469454393135295000000000000)
      constant := (6147201262639231007707039736174976477061053385409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree028.table
  base := (-7359318098935701445699942183571173368157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-99371697886389778567317792717662255000000000000)
      constant := (686374090008254569892818134465219608076243398027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129884635920100739431/50000000000000000000)
  centralHi := (259769271840201478863/100000000000000000000)
  directionLo := (264536078095840847023/100000000000000000000)
  directionHi := (16533504880990052939/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree029.table
  base := (-898900695826810062572026892874857991591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-924054600825649339229323982119041795000000000000)
      constant := (6612245488518892788931438933178370092546850588872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree029.table
  base := (-7197250671152845469046897074378449778373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-102918094381146038327664290560484505000000000000)
      constant := (738293219074713506675615022800120980371326120803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264536078095840847023/100000000000000000000)
  centralHi := (16533504880990052939/6250000000000000000)
  directionLo := (53843699217742876821/20000000000000000000)
  directionHi := (134609248044357192053/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree030.table
  base := (-1395696262241779225836844296494452980717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-106210669197205170993797612204994255000000000000)
      constant := (788312412048455131643693318731956848032655000935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree030.table
  base := (-6983781821571832551374652091613926478559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-106464490875902298088010788403306755000000000000)
      constant := (792167547904125182442888991807993328601751476249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53843699217742876821/20000000000000000000)
  centralHi := (134609248044357192053/50000000000000000000)
  directionLo := (273820855046158667657/100000000000000000000)
  directionHi := (136910427523079333829/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree031.table
  base := (-839536394703076816592535735340385740121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-987737444724043738659033037570854795000000000000)
      constant := (7594846008963135916907262532361650230653054328632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree031.table
  base := (-3360466818144151023653718120968095036641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-110010887370658557848357286246129005000000000000)
      constant := (847991115206713989865305252820825546843048141902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273820855046158667657/100000000000000000000)
  centralHi := (136910427523079333829/50000000000000000000)
  directionLo := (278347126229371642933/100000000000000000000)
  directionHi := (139173563114685821467/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree032.table
  base := (-400397352815034159669574183219161164203/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1019578866673240938373887565296761295000000000000)
      constant := (8112302686310763240467007672518514759092375638352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree032.table
  base := (-256416782356143050039667424701624153797/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-113557283865414817608703784088951255000000000000)
      constant := (905758869598246750302035933206013498751418901675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278347126229371642933/100000000000000000000)
  centralHi := (139173563114685821467/50000000000000000000)
  directionLo := (282800963050146039989/100000000000000000000)
  directionHi := (28280096305014603999/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree033.table
  base := (-6050141053674313393270847230229563331213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-116824476513604237565415788113629755000000000000)
      constant := (960793666128284419503122692676852859368447598043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree033.table
  base := (-1513422884544082928283559041161440000817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-117103680360171077369050281931773505000000000000)
      constant := (965466530604559445759384267685705561037725645148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282800963050146039989/100000000000000000000)
  centralHi := (28280096305014603999/10000000000000000000)
  directionLo := (57437147117185540227/20000000000000000000)
  directionHi := (17949108474120481321/6250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree034.table
  base := (-706109919315220345051216524453051697101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (7161102)
      previous := (3580551)
      next := (3580551)
      square := (108575955734441660536365724360500000000000000)
      linear := (-3748310417202890442226977926465655000000000000)
      constant := (31831605843101899387272818987804813213926834328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree034.table
  base := (-5651979955079659487954241042568082859807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12063995081604628948485080484500000000000000)
      linear := (-417474314376911201139781244894795000000000000)
      constant := (3554015470425742204859544523327355486747108793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57437147117185540227/20000000000000000000)
  centralHi := (17949108474120481321/6250000000000000000)
  directionLo := (14575228021026866161/5000000000000000000)
  directionHi := (291504560420537323221/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree035.table
  base := (-5203622063587827424685815969894565654983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1115103132520832537518451148474480795000000000000)
      constant := (9768848120217125486481754313394031135994901402617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree035.table
  base := (-260316372199388287513615736883852779047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-124196473349683596889743277617418005000000000000)
      constant := (1090687616864757285529387501333207499389442176340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14575228021026866161/5000000000000000000)
  centralHi := (291504560420537323221/100000000000000000000)
  directionLo := (295760326561746630539/100000000000000000000)
  directionHi := (14788016328087331527/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree036.table
  base := (-589407366935511893450364459932443440809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-127438283830003304137033964022265255000000000000)
      constant := (1150629053572726819537535207921257211992230687992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree036.table
  base := (-4717617546336615377978725298144889681767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-127742869844439856650089775460240255000000000000)
      constant := (1156195363580924398473427027520642885322969206737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295760326561746630539/100000000000000000000)
  centralHi := (14788016328087331527/5000000000000000000)
  directionLo := (37494464756033348901/12500000000000000000)
  directionHi := (299955718048266791209/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree037.table
  base := (-2092272142781268421980494207120537564201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1178785976419226936948160203926293795000000000000)
      constant := (10959754160369571501749857144892010340092060285998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree037.table
  base := (-4186598988679029420372736094439784733369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-131289266339196116410436273303062505000000000000)
      constant := (1223631503789026456382119329753331669465186918159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37494464756033348901/12500000000000000000)
  centralHi := (299955718048266791209/100000000000000000000)
  directionLo := (4751456777324725703/1562500000000000000)
  directionHi := (304093233748782444993/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree038.table
  base := (-722423521573961325830991196323455122891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1210627398368424136663014731652200295000000000000)
      constant := (11581109187293935305858270637470393252959512761545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree038.table
  base := (-722781250909007889026340238727351123903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-134835662833952376170782771145884755000000000000)
      constant := (1292994166975147892021142044957024738262419643165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4751456777324725703/1562500000000000000)
  centralHi := (304093233748782444993/100000000000000000000)
  directionLo := (308175204767891657743/100000000000000000000)
  directionHi := (19260950297993228609/6250000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree039.table
  base := (-1499260526862263727820919739434486657359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-138052091146402370708652139930900755000000000000)
      constant := (1357745797570509319752386971911056654829586326098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree039.table
  base := (-1500038508256777895586903056612802513427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-138382059328708635931129268988707005000000000000)
      constant := (1364281768032673218188344198507651096801987017994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308175204767891657743/100000000000000000000)
  centralHi := (19260950297993228609/6250000000000000000)
  directionLo := (19512738112703962483/6250000000000000000)
  directionHi := (312203809803263399729/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree040.table
  base := (-93768569971097819959738637254039228073/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1274310242266818536092723787104013295000000000000)
      constant := (12875550937722325073211535126409199067883636938175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree040.table
  base := (-2345566908032702165846955340734063751263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-141928455823464895691475766831529255000000000000)
      constant := (1437492963713645989311454214012479604729602813593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19512738112703962483/6250000000000000000)
  centralHi := (312203809803263399729/100000000000000000000)
  directionLo := (31618108874126640633/10000000000000000000)
  directionHi := (316181088741266406331/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree041.table
  base := (-103099178584840789942178136944452649323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1306151664216015735807578314829919795000000000000)
      constant := (13548615127210862806879453429168028219325440900432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree041.table
  base := (-1650762041128502632562800233107381328039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-145474852318221155451822264674351505000000000000)
      constant := (1512626615725449516135392899634264898288002832529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31618108874126640633/10000000000000000000)
  centralHi := (316181088741266406331/100000000000000000000)
  directionLo := (160054477365952572099/50000000000000000000)
  directionHi := (320108954731905144199/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree042.table
  base := (-114371153385973158920691843647330497047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-148665898462801437280270315839536255000000000000)
      constant := (1582099553501405524779780183887831515658329654536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree042.table
  base := (-915989614054723039556179263664877972919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-149021248812977415212168762517173755000000000000)
      constant := (1589681759458511052354403458653037496061695198209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160054477365952572099/50000000000000000000)
  centralHi := (320108954731905144199/100000000000000000000)
  directionLo := (323989204945925955097/100000000000000000000)
  directionHi := (161994602472962977549/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree043.table
  base := (-35160355602166947768566044422565340647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1369834508114410135237287370281732795000000000000)
      constant := (14946386069746892571853820830684222153128463751012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree043.table
  base := (-141526900380622020963995981730060327441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-152567645307733674972515260359996005000000000000)
      constant := (1668657577485671075851031861220975810679334789751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323989204945925955097/100000000000000000000)
  centralHi := (161994602472962977549/50000000000000000000)
  directionLo := (327823530185728928437/100000000000000000000)
  directionHi := (163911765092864464219/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree044.table
  base := (673159123705751099275889226769138256099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1401675930063607334952141898007639295000000000000)
      constant := (15671079092151737427718398081095347148290561803299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree044.table
  base := (672391133494011586778639585446446309009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-156114041802489934732861758202818255000000000000)
      constant := (1749553377105070999554260960252952573452680033801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327823530185728928437/100000000000000000000)
  centralHi := (163911765092864464219/50000000000000000000)
  directionLo := (331613523495912091063/100000000000000000000)
  directionHi := (41451690436989011383/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree045.table
  base := (763115560065010490658653591831138062737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-159279705779200503851888491748171755000000000000)
      constant := (1823663300878867738736204293949155648460472519186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree045.table
  base := (762782686554178448439541814972914586413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-159660438297246194493208256045640505000000000000)
      constant := (1832368571309559136476767117257924219580287429514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331613523495912091063/100000000000000000000)
  centralHi := (41451690436989011383/12500000000000000000)
  directionLo := (83840171974460636179/25000000000000000000)
  directionHi := (335360687897842544717/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree046.table
  base := (604600979054068936587630398543737573207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1465358773962001734381850953459452295000000000000)
      constant := (17172053389181428882039375168153697660304497051228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree046.table
  base := (7555709642647996528898887133511853927/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-163206834792002454253554753888462755000000000000)
      constant := (1917102662659779483879429131444136222438174560960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83840171974460636179/25000000000000000000)
  centralHi := (335360687897842544717/100000000000000000000)
  directionLo := (169533221677385749483/50000000000000000000)
  directionHi := (339066443354771498967/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree047.table
  base := (1674766418908088917763702292794441524379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1497200195911198934096705481185358795000000000000)
      constant := (17948326297356207443029264482859850229244969311158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree047.table
  base := (1674516642151002317874451826408178123101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-166753231286758714013901251731285005000000000000)
      constant := (2003755229617893245647953190354541266369509407978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169533221677385749483/50000000000000000000)
  centralHi := (339066443354771498967/100000000000000000000)
  directionLo := (342732133059033121273/100000000000000000000)
  directionHi := (171366066529516560637/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree048.table
  base := (86389904664616084984648568194481349459/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-169893513095599570423506667656807255000000000000)
      constant := (2082420575349002832859153857267602256352261692550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree048.table
  base := (4319062799931323637882271991639955982899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-170299627781514973774247749574107255000000000000)
      constant := (2092325914966488787206385185320120586193668730011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342732133059033121273/100000000000000000000)
  centralHi := (171366066529516560637/50000000000000000000)
  directionLo := (346359029120268638483/100000000000000000000)
  directionHi := (86589757280067159621/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree049.table
  base := (1065637424205286574920353335834956094219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1560883039809593333526414536637171795000000000000)
      constant := (19552427272617194396638820420163822936958249887095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree049.table
  base := (5327812952106447217565063974613503069087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-173846024276271233534594247416929505000000000000)
      constant := (2182814415994523245522425011824250842649441624743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346359029120268638483/100000000000000000000)
  centralHi := (86589757280067159621/25000000000000000000)
  directionLo := (87487084430744480769/25000000000000000000)
  directionHi := (349948337722977923077/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree050.table
  base := (6375520348103273699038283787391720474347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1592724461758790533241269064363078295000000000000)
      constant := (20380250241836059884202544304907471203393474555947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree050.table
  base := (3187598364041856752319147460408269751351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-177392420771027493294940745259751755000000000000)
      constant := (2275220476180684171216937538877941923625981236478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87487084430744480769/25000000000000000000)
  centralHi := (349948337722977923077/100000000000000000000)
  directionLo := (353501203812682549987/100000000000000000000)
  directionHi := (88375300953170637497/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree051.table
  base := (466338761271825635350831671533093675043/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12063995081604628948485080484500000000000000)
      linear := (-624592804193766910017733022717795000000000000)
      constant := (8160419878082390333767690395234802917265818288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree051.table
  base := (7461140392207745089178693901633537379529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12063995081604628948485080484500000000000000)
      linear := (-626085872891985304689575235649045000000000000)
      constant := (8199113765210024354176053566133296214808575329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353501203812682549987/100000000000000000000)
  centralHi := (88375300953170637497/25000000000000000000)
  directionLo := (3570187153623126833/1000000000000000000)
  directionHi := (357018715362312683301/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree052.table
  base := (4292911630016435127798208151186818738099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1656407305657184932670978119814891295000000000000)
      constant := (22087431174727828213190533172899132140802103770598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree052.table
  base := (8585581460070175185798334397956528052813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-184485213760540012815633740945396255000000000000)
      constant := (2465784437679964869314283330124202397830689424357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3570187153623126833/1000000000000000000)
  centralHi := (357018715362312683301/100000000000000000000)
  directionLo := (72100381452776338811/20000000000000000000)
  directionHi := (45062738407985211757/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree053.table
  base := (4874337937056511427058065663930003262053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1688248727606382132385832647540797795000000000000)
      constant := (22966786032185218659418962520108855381462806200906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree053.table
  base := (9748466981770190778514223307057002781431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-188031610255296272575980238788218505000000000000)
      constant := (2563941998682467526145672801259751512272906135359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72100381452776338811/20000000000000000000)
  centralHi := (45062738407985211757/12500000000000000000)
  directionLo := (363951764884904317569/100000000000000000000)
  directionHi := (36395176488490431757/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree054.table
  base := (342185390191823438054029202881184617523/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-191121127728397703566743019474078255000000000000)
      constant := (2651479496339429725737103851067781882692440433504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree054.table
  base := (10949752087114620995469061775851389973547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-191578006750052532336326736631040755000000000000)
      constant := (2664016428871882093928604981700681655915724201683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363951764884904317569/100000000000000000000)
  centralHi := (36395176488490431757/10000000000000000000)
  directionLo := (183684613662098128687/50000000000000000000)
  directionHi := (2938953818593570059/800000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree055.table
  base := (1218955449161531848492600704296046461771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1751931571504776531815541702992610795000000000000)
      constant := (24777018455051430206020955143699466246069240505710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree055.table
  base := (12189398752791223581852583466928471801519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-195124403244808792096673234473863005000000000000)
      constant := (2766007616152100007706338528170600529004868347191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183684613662098128687/50000000000000000000)
  centralHi := (2938953818593570059/800000000000000000)
  directionLo := (370755190397541569733/100000000000000000000)
  directionHi := (185377595198770784867/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree056.table
  base := (13467509162829043325032312811632536570227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1783772993453973731530396230718517295000000000000)
      constant := (25707894127816960455976524442050128597943055515827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree056.table
  base := (13467374757646804677073385390210288573441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-198670799739565051857019732316685255000000000000)
      constant := (2869915465532293969343596392019892189430187104249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370755190397541569733/100000000000000000000)
  centralHi := (185377595198770784867/50000000000000000000)
  directionLo := (18705525469006318131/5000000000000000000)
  directionHi := (374110509380126362621/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree057.table
  base := (3695942188569902433122521740034025618277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-201734935044796770138361195382713755000000000000)
      constant := (2961771305465070044049758298467611404703842490612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree057.table
  base := (14783652797369372160110540044142128623439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-202217196234321311617366230159507505000000000000)
      constant := (2975739896516922142300310108111425708831345658071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18705525469006318131/5000000000000000000)
  centralHi := (374110509380126362621/100000000000000000000)
  directionLo := (47179500191191011087/12500000000000000000)
  directionHi := (377436001529528088697/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree058.table
  base := (16138309744285794560903652026043069455283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1847455837352368130960105286170330295000000000000)
      constant := (27621160695061352948254945498803798814286202237683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree058.table
  base := (16138209734252632916108493170565178566081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-205763592729077571377712728002329755000000000000)
      constant := (3083480840893967118613798280347819929213699169209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47179500191191011087/12500000000000000000)
  centralHi := (377436001529528088697/100000000000000000000)
  directionLo := (380732448410347925083/100000000000000000000)
  directionHi := (95183112102586981271/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree059.table
  base := (1095694512001841687900657160052212682297/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1879297259301565330674959813896236795000000000000)
      constant := (28603550436358368869587033309802684356845000382352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree059.table
  base := (8765512980716050270671517661757350788803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-209309989223833831138059225845152005000000000000)
      constant := (3193138240860647381426592007827730115559222894934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380732448410347925083/100000000000000000000)
  centralHi := (95183112102586981271/25000000000000000000)
  directionLo := (384000598039219932179/100000000000000000000)
  directionHi := (19200029901960996609/5000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree060.table
  base := (18962159192468847643053213812796873798121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-212348742361195836709979371291349255000000000000)
      constant := (3289234502726507636694362730957173572878628740769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree060.table
  base := (18962084864126827602627627478319606913937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-212856385718590090898405723687974255000000000000)
      constant := (3304712047435109982201335819904452696627301616393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384000598039219932179/100000000000000000000)
  centralHi := (19200029901960996609/5000000000000000000)
  directionLo := (387241166866874929081/100000000000000000000)
  directionHi := (193620583433437464541/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree061.table
  base := (63848238794448394533431847988718410307/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1942980103199959730104668869348049795000000000000)
      constant := (30619840579350286989260429406112769996727833570240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree061.table
  base := (20431372363085706214166994827890170451349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-216402782213346350658752221530796505000000000000)
      constant := (3418202219110469601542103410667229334715747022061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387241166866874929081/100000000000000000000)
  centralHi := (193620583433437464541/50000000000000000000)
  directionLo := (390454841612137251693/100000000000000000000)
  directionHi := (195227420806068625847/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree062.table
  base := (21938931707801377192074571654555863078121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-1974821525149156929819523397073956295000000000000)
      constant := (31653740278433470009955941468576764123435031946921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree062.table
  base := (10969438263847800843914989017430102679821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-219949178708102610419098719373618755000000000000)
      constant := (3533608720714216893819296878716323485458501624138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390454841612137251693/100000000000000000000)
  centralHi := (195227420806068625847/50000000000000000000)
  directionLo := (393642280961153234819/100000000000000000000)
  directionHi := (19682114048057661741/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree063.table
  base := (23484634773461035977315621862221612839203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-222962549677594903281597547199984755000000000000)
      constant := (3633867705389680736991286691878672679873513133067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree063.table
  base := (11742293624061167781175356974846123315589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-223495575202858870179445217216441005000000000000)
      constant := (3650931522441660925687221406825078393178662918842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393642280961153234819/100000000000000000000)
  centralHi := (19682114048057661741/5000000000000000000)
  directionLo := (79360823428752254107/20000000000000000000)
  directionHi := (49600514642970158817/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree064.table
  base := (6267134219907787254545873770512193196513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2038504369047551329249232452525769295000000000000)
      constant := (33773047557898212777412034948711093640626533291652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree064.table
  base := (3133561994684661233869303048483426081177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-227041971697615129939791715059263255000000000000)
      constant := (3770170599036851598292825905950273960897848166024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79360823428752254107/20000000000000000000)
  centralHi := (49600514642970158817/12500000000000000000)
  directionLo := (12498154918677782967/3125000000000000000)
  directionHi := (79988191479537810989/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree065.table
  base := (26690630624192120536212366554220071270363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2070345790996748528964086980251675795000000000000)
      constant := (34858454710207762230436831820332778223722358676763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree065.table
  base := (834081106136772375552645959869597375867/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-230588368192371389700138212902085505000000000000)
      constant := (3891325929098479535621605754877141121663115781216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/3125000000000000000)
  centralHi := (79988191479537810989/20000000000000000000)
  directionLo := (403053385330182341789/100000000000000000000)
  directionHi := (40305338533018234179/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree066.table
  base := (442982964563988073210219956807620988851/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-233576356993993969853215723108620255000000000000)
      constant := (3995670070993461800246164853507507898417648367296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree066.table
  base := (3543859926678181681834847934489191795813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-234134764687127649460484710744907755000000000000)
      constant := (4014397494491684330209173044266922848117012410856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403053385330182341789/100000000000000000000)
  centralHi := (40305338533018234179/10000000000000000000)
  directionLo := (40614196218571254733/10000000000000000000)
  directionHi := (406141962185712547331/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree067.table
  base := (30049368883788260076900197117827327012601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2134028634895142928393796035703488795000000000000)
      constant := (37080775202955773769000670271674211097487266825401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree067.table
  base := (30049342796143689398145661053356833317171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-237681161181883909220831208587730005000000000000)
      constant := (4139385279849611583265573849151233965877185336219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40614196218571254733/10000000000000000000)
  centralHi := (406141962185712547331/100000000000000000000)
  directionLo := (409207228027561941393/100000000000000000000)
  directionHi := (204603614013780970697/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree068.table
  base := (6357200713951639633330561266738755622519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (7161102)
      previous := (3580551)
      next := (3580551)
      square := (108575955734441660536365724360500000000000000)
      linear := (-7494360058284913938092216482454655000000000000)
      constant := (132241135925957107587234132589996882074739234355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree068.table
  base := (1589299056384586673448361096459500933913/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12063995081604628948485080484500000000000000)
      linear := (-834697431407059408239369226403295000000000000)
      constant := (14762246616439532141248181050875102380536930260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409207228027561941393/100000000000000000000)
  centralHi := (204603614013780970697/50000000000000000000)
  directionLo := (412249702840331214021/100000000000000000000)
  directionHi := (206124851420165607011/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree069.table
  base := (8390202491803941358312225872952579398399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-244190164310393036424833899017255755000000000000)
      constant := (4374641086272148866185811864143273119884186838044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree069.table
  base := (1342431626618260641924343521177575074861/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-244773954171396428741524204273374505000000000000)
      constant := (4395109460362367525074513553255711623121797265725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412249702840331214021/100000000000000000000)
  centralHi := (206124851420165607011/50000000000000000000)
  directionLo := (41526988755974313287/10000000000000000000)
  directionHi := (415269887559743132871/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree070.table
  base := (17686892417775594342071385464128124323309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2229552900742734527538359618881208295000000000000)
      constant := (40543019598516526647112647437836295847347234717018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree070.table
  base := (17686884119082058196262760576171033597257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-248320350666152688501870702116196755000000000000)
      constant := (4525845835134442030297500992653658260033407583746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41526988755974313287/10000000000000000000)
  centralHi := (415269887559743132871/100000000000000000000)
  directionLo := (104567066258879407197/25000000000000000000)
  directionHi := (418268265035517628789/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree071.table
  base := (9306231356926006193513318445832378502171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2261394322691931727253214146607114795000000000000)
      constant := (41731437675915956574086127859862974620119124843884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree071.table
  base := (37224911158691585567055470402026087737599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-251866747160908948262217199959019005000000000000)
      constant := (4658498388545370697086372212388684104472250498311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104567066258879407197/25000000000000000000)
  centralHi := (418268265035517628789/100000000000000000000)
  directionLo := (210622650466279583789/50000000000000000000)
  directionHi := (421245300932559167579/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree072.table
  base := (1955711470751229541359782000411571883147/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-254803971626792102996452074925891255000000000000)
      constant := (4770780438540225660237382551974261870828299121660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree072.table
  base := (39114217150182631981180517393113589503141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-255413143655665208022563697801841255000000000000)
      constant := (4793067113882778537622328832965958958964725447549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210622650466279583789/50000000000000000000)
  centralHi := (421245300932559167579/100000000000000000000)
  directionLo := (26512590285951191249/6250000000000000000)
  directionHi := (84840288915043811997/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree073.table
  base := (10260423705893333746826567196096213544111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2325077166590326126682923202058927795000000000000)
      constant := (44159778358980604435832170037489697465777607539644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree073.table
  base := (41041684283437232414019950384821291328701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-258959540150421467782910195644663505000000000000)
      constant := (4929552005459212184648147857790308780931938802389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512590285951191249/6250000000000000000)
  centralHi := (84840288915043811997/20000000000000000000)
  directionLo := (53392141217370850923/12500000000000000000)
  directionHi := (85427425947793361477/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree074.table
  base := (5375914997514634722754681990754519336279/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2356918588539523326397777729784834295000000000000)
      constant := (45399700867876114077636222431059528966201142299832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree074.table
  base := (4300731092385495966912782105914273610633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-262505936645177727543256693487485755000000000000)
      constant := (5067953058455724099350686147530850232244974303370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53392141217370850923/12500000000000000000)
  centralHi := (85427425947793361477/20000000000000000000)
  directionLo := (430052775393419914581/100000000000000000000)
  directionHi := (215026387696709957291/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree075.table
  base := (45011103466346073533099667737294220371151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-265417778943191169568070250834526755000000000000)
      constant := (5184087937324092181011770436726886418339766180439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree075.table
  base := (9002219137294857644888902867334178335187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-266052333139933987303603191330308005000000000000)
      constant := (5208270268789324442915140493627749314870015538215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430052775393419914581/100000000000000000000)
  centralHi := (215026387696709957291/50000000000000000000)
  directionLo := (54118598300041974763/12500000000000000000)
  directionHi := (86589757280067159621/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree076.table
  base := (47053044080060520637958909246791569845953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2420601432437917725827486785236647295000000000000)
      constant := (47931050031205022992081788951626749781200271604353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree076.table
  base := (5881629674734070247646345869582140294971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-269598729634690247063949689173130255000000000000)
      constant := (5350503633000658790545857874853888844200486083352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54118598300041974763/12500000000000000000)
  centralHi := (86589757280067159621/20000000000000000000)
  directionLo := (43582555416985808759/10000000000000000000)
  directionHi := (435825554169858087591/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree077.table
  base := (24566570401132814656037790983039140285707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2452442854387114925542341312962553795000000000000)
      constant := (49222476626703908189173765450999902421323493950614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree077.table
  base := (307082094149248711552750107014077887721/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-273145126129446506824296187015952505000000000000)
      constant := (5494653148158825539170112579908158148549362427040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43582555416985808759/10000000000000000000)
  centralHi := (435825554169858087591/100000000000000000000)
  directionLo := (219341728639014457843/50000000000000000000)
  directionHi := (438683457278028915687/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree078.table
  base := (51251392769275841190542314906627946670773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-276031586259590236139688426743162255000000000000)
      constant := (5614563466610832019301321196754410141672692502797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree078.table
  base := (51251387842219193500186396816838566860047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-276691522624202766584642684858774755000000000000)
      constant := (5640718811780717748272323410015312871235869100183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219341728639014457843/50000000000000000000)
  centralHi := (438683457278028915687/100000000000000000000)
  directionLo := (27595178878020334213/6250000000000000000)
  directionHi := (441522862048325347409/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree079.table
  base := (13351949812266425086529798179468807693397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2516125698285509324972050368414366795000000000000)
      constant := (51856833730163077196644437757742721008444686459988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree079.table
  base := (13351948754830668804760188653252742964933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-280237919118959026344989182701597005000000000000)
      constant := (5788700621762673193598057260912887610518985452148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27595178878020334213/6250000000000000000)
  centralHi := (441522862048325347409/100000000000000000000)
  directionLo := (444344123099748951713/100000000000000000000)
  directionHi := (222172061549874475857/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree080.table
  base := (27801179810610470661284959027898703091323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2547967120234706524686904896140273295000000000000)
      constant := (53199764202239347015059914525453208074560315971446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree080.table
  base := (27801177995342150398941801881884988884161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-283784315613715286105335680544419255000000000000)
      constant := (5938598576322554568284225452036406769989034636658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444344123099748951713/100000000000000000000)
  centralHi := (222172061549874475857/50000000000000000000)
  directionLo := (447147583863790059621/100000000000000000000)
  directionHi := (223573791931895029811/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree081.table
  base := (57835073359941758729124600211114849005941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-286645393575989302711306602651797755000000000000)
      constant := (6062206955752817336298477369660009706591075596749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree081.table
  base := (28917535122105907070001035202253013890807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-287330712108471545865682178387241505000000000000)
      constant := (6090412673950668325146925823787227425936670635646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447147583863790059621/100000000000000000000)
  centralHi := (223573791931895029811/50000000000000000000)
  directionLo := (112483394268100046703/25000000000000000000)
  directionHi := (449933577072400186813/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree082.table
  base := (7513242502454205498578340671637071788413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2611649964133100924116613951592086295000000000000)
      constant := (55937128916948233808753096235409481974877409878504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree082.table
  base := (6010593734611879482611036422492179914131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-290877108603227805626028676230063755000000000000)
      constant := (6244142913368173489798686549895255454408705456590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112483394268100046703/25000000000000000000)
  centralHi := (449933577072400186813/100000000000000000000)
  directionLo := (45270242521893539511/10000000000000000000)
  directionHi := (452702425218935395111/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree083.table
  base := (31207479611345948919781702367063668491441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2643491386082298123831468479317992795000000000000)
      constant := (57331563137739070019089745813193809338326748512482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree083.table
  base := (31207478464484880203552637197993028457293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-294423505097984065386375174072886005000000000000)
      constant := (6399789293491837558221613394650742991043264926154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45270242521893539511/10000000000000000000)
  centralHi := (452702425218935395111/100000000000000000000)
  directionLo := (22772722049693911601/5000000000000000000)
  directionHi := (455454440993878232021/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree084.table
  base := (64762130649145884994336242260471913904633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-297259200892388369282924778560433255000000000000)
      constant := (6527018361739794162862979894490087054191195596337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree084.table
  base := (64762128681549699171161064453140569262081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-297969901592740325146721671915708255000000000000)
      constant := (6557351813404170977753201734465627022695279113209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22772722049693911601/5000000000000000000)
  centralHi := (455454440993878232021/100000000000000000000)
  directionLo := (458189927697004730577/100000000000000000000)
  directionHi := (229094963848502365289/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree085.table
  base := (33573727013939964290644900701011257036941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (7161102)
      previous := (3580551)
      next := (3580551)
      square := (108575955734441660536365724360500000000000000)
      linear := (-9367384878825925686024835760449155000000000000)
      constant := (208207388455058850679475362313177397494609032538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree085.table
  base := (6714745234027964166857303166815242416173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (795678)
      previous := (397839)
      next := (397839)
      square := (12063995081604628948485080484500000000000000)
      linear := (-1043308989922133511789163217157545000000000000)
      constant := (23241627931931209300786993363247522878873807730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458189927697004730577/100000000000000000000)
  centralHi := (229094963848502365289/50000000000000000000)
  directionLo := (230454589813767181393/50000000000000000000)
  directionHi := (460909179627534362787/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree086.table
  base := (69570929129190835851639144688706276612071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2739015651929889722976032062495712295000000000000)
      constant := (61617873155205982058626274049795375829799034040871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree086.table
  base := (69570927681942357456461927999454138528553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-305062694582252844667414667601352755000000000000)
      constant := (6878225269605618827065213997709847619300503285217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230454589813767181393/50000000000000000000)
  centralHi := (460909179627534362787/100000000000000000000)
  directionLo := (115903120613420891361/25000000000000000000)
  directionHi := (92722496490736713089/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree087.table
  base := (18008138939619645215658600820039918167317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-307873008208787435854542954469068755000000000000)
      constant := (7008997658397420704400742490172737896739869628852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree087.table
  base := (18008138629379565082755885380264647478637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-308609091077009104427761165444175005000000000000)
      constant := (7041536204679422432294533526326896094782589898772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115903120613420891361/25000000000000000000)
  centralHi := (92722496490736713089/20000000000000000000)
  directionLo := (93260022712587276401/20000000000000000000)
  directionHi := (233150056781468191003/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree088.table
  base := (1863308343772441073314935140430038611109/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2802698495828284122405741117947525295000000000000)
      constant := (64561252570250607293321253521762450215634859452360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree088.table
  base := (37266166343481054836817000177901124723939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-312155487571765364188107663286997255000000000000)
      constant := (7206763277077702690245281436011204387772545205142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93260022712587276401/20000000000000000000)
  centralHi := (233150056781468191003/50000000000000000000)
  directionLo := (468972342394247894473/100000000000000000000)
  directionHi := (234486171197123947237/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree089.table
  base := (77070262966822758096327064032992496441039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2834539917777481322120595645673431795000000000000)
      constant := (66058694085522795576408835996370999285063296020239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree089.table
  base := (7707026205477694548577463717428684190493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-315701884066521623948454161129819505000000000000)
      constant := (7373906486401002503612384827314314066464663178770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468972342394247894473/100000000000000000000)
  centralHi := (234486171197123947237/50000000000000000000)
  directionLo := (117907357688326642101/25000000000000000000)
  directionHi := (94325886150661313681/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree090.table
  base := (79646343288005102216177123106556800168707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-318486815525186502426161130377704255000000000000)
      constant := (7508144829806208741060140570211152005452563250923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree090.table
  base := (79646342506263600396589647074407686447111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-319248280561277883708800658972641755000000000000)
      constant := (7542965832311178518760664781218184244430177020879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117907357688326642101/25000000000000000000)
  centralHi := (94325886150661313681/20000000000000000000)
  directionLo := (94854326622379921899/20000000000000000000)
  directionHi := (59283954138987451187/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree091.table
  base := (41130287307156898616915774074868318797683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2898222761675875721550304701125244795000000000000)
      constant := (69105080715793103911241975184860568065226964600166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree091.table
  base := (82260573944342695209002498463163380434447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-322794677056034143469147156815464005000000000000)
      constant := (7713941314522032085752391142775335009561608421783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94854326622379921899/20000000000000000000)
  centralHi := (59283954138987451187/12500000000000000000)
  directionLo := (476899196892350223031/100000000000000000000)
  directionHi := (59612399611543777879/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree092.table
  base := (3396518274438945283213998176045902771407/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2930064183625072921265159228851151295000000000000)
      constant := (70654025825885147496485773645514353517477260525175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree092.table
  base := (84912956286861755394611944072582947842967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-326341073550790403229493654658286255000000000000)
      constant := (7886832932791370398107604007328781075123424740063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476899196892350223031/100000000000000000000)
  centralHi := (59612399611543777879/12500000000000000000)
  directionLo := (479512362737926642479/100000000000000000000)
  directionHi := (5993904534224083031/1250000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree093.table
  base := (1752069799124469085694375097217486810309/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-329100622841585568997779306286339755000000000000)
      constant := (8024459866291998338580955415744087326155852475050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree093.table
  base := (43801744732156708264613320947848366050937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-329887470045546662989840152501108505000000000000)
      constant := (8061640686914279559348353545612537273245481618786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479512362737926642479/100000000000000000000)
  centralHi := (5993904534224083031/1250000000000000000)
  directionLo := (120527841192514845269/25000000000000000000)
  directionHi := (482111364770059381077/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree094.table
  base := (22583043459832797014839407319887273117639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-2993747027523467320694868284302964295000000000000)
      constant := (73803419626410224482281663564715117545251860707356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree094.table
  base := (90332173417901983213995477276928726697989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-333433866540302922750186650343930755000000000000)
      constant := (8238364576717424626621936173872761190462347693021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120527841192514845269/25000000000000000000)
  centralHi := (482111364770059381077/100000000000000000000)
  directionLo := (484696430833144848621/100000000000000000000)
  directionHi := (242348215416572424311/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree095.table
  base := (93099008458911183890063752961300896147887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-3025588449472664520409722812028870795000000000000)
      constant := (75403868313868460588828877893275919466113552341487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree095.table
  base := (3723960323916207156236752564848451166473/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-336980263035059182510533148186753005000000000000)
      constant := (8417004602054219903396976637933580926272905502425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484696430833144848621/100000000000000000000)
  centralHi := (242348215416572424311/50000000000000000000)
  directionLo := (9745355654553196097/2000000000000000000)
  directionHi := (487267782727659804851/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree096.table
  base := (1498499902679654216755211928262895165617/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-339714430157984635569397482194975255000000000000)
      constant := (8557942761983269999686317522205238822138153978432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree096.table
  base := (23975998365571509071646663357724943994419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-340526659529815442270879646029575255000000000000)
      constant := (8597560762800736668728710922260029369662250861164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9745355654553196097/2000000000000000000)
  centralHi := (487267782727659804851/100000000000000000000)
  directionLo := (244912818216130838249/50000000000000000000)
  directionHi := (489825636432261676499/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree097.table
  base := (24686782435084170527971508783784236732459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-3089271293371058919839431867480683795000000000000)
      constant := (78656269257377931177676859497106697523136899550636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree097.table
  base := (6171695592219797012575204619570791942193/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-344073056024571702031226143872397505000000000000)
      constant := (8780033058852235796942320463661555618137085106832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell093.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244912818216130838249/50000000000000000000)
  centralHi := (489825636432261676499/100000000000000000000)
  directionLo := (98474040463100834819/20000000000000000000)
  directionHi := (30773137644719010881/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree098.table
  base := (20325683266871838391109456240274298017701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2069558478)
      previous := (1034779239)
      next := (1034779239)
      square := (31378451207253639895009694340184500000000000000)
      linear := (-3121112715320256119554286395206590295000000000000)
      constant := (80308221511629631695491522524509176208591775552505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree098.table
  base := (10162841610758215666744072133321890911217/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (229950942)
      previous := (114975471)
      next := (114975471)
      square := (3486494578583737766112188260020500000000000000)
      linear := (-347619452519327961791572641715219755000000000000)
      constant := (8964421490120229895579774025866363553045588143130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell093.Kernel098
