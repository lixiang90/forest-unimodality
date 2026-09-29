import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell184.Parameters
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch050_099
import ForestUnimodality.BinomialMassData.Q427_792.Batch000_049
import ForestUnimodality.BinomialMassData.Q427_792.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree000.table
  base := (22306307121278379183149099/625000000000000000000000)
  polynomial :=
    { denominator := 47520000000000000000000000000000000000000000
      center := (202003)
      previous := (0)
      next := (173405)
      square := (7872764035321480320384068793600000000000000)
      linear := (-30184568119640843395501406040000000000000000)
      constant := (1695993143045037726053192295168000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree000.table
  base := (22306307121278379183149099/625000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (33733)
      previous := (0)
      next := (28835)
      square := (1312127339220246720064011465600000000000000)
      linear := (-5030761353273473899250234340000000000000000)
      constant := (282665523840839621008865382528000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree001.table
  base := (224815680947323190552751614030938202698987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-3827049645440986211955558527344800000000000000)
      constant := (107597713109079747714863519219942090583333036176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree001.table
  base := (224560903618853718458116610223067832328617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-212704989145278417797535474537600000000000000)
      constant := (5971215625842215839354847530164150865740733912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6230819941265383747/12500000000000000000)
  directionHi := (49846559530123069977/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree002.table
  base := (72870827975774207369978748399082377429333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-4665827047037528927756477856729600000000000000)
      constant := (72682458919107769890298323761119112593749702368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree002.table
  base := (36359836715887450575190355764295148969041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-259394853632532196919813215855200000000000000)
      constant := (4030558906911176734951760269253672053819422304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6230819941265383747/12500000000000000000)
  centralHi := (49846559530123069977/100000000000000000000)
  directionLo := (1409873610502757953/2000000000000000000)
  directionHi := (70493680525137897651/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree003.table
  base := (97180218046281326705530946440502033094589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-611622716514896849284155242901600000000000000)
      constant := (5841458598128642145222237434038197273920356208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree003.table
  base := (48452687499134685044926532626975953647011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-102028239373261992014030319057600000000000000)
      constant := (971503915410506800508347815349579016345519664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/2000000000000000000)
  centralHi := (70493680525137897651/100000000000000000000)
  directionLo := (86336773688679780039/100000000000000000000)
  directionHi := (2158419342216994501/2500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree004.table
  base := (16607899000537124780288671142005511072337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-6343381850230614359358316515499200000000000000)
      constant := (41295136525913505825216751671631234691835187904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree004.table
  base := (8275481196865075850461813642660304852213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-352774582607039755164368698490400000000000000)
      constant := (2289705845323919161667623545311357820939511744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/100000000000000000000)
  centralHi := (2158419342216994501/2500000000000000000)
  directionLo := (6230819941265383747/6250000000000000000)
  directionHi := (99693119060246139953/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree005.table
  base := (5783969618283928388244704259637848704967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-7182159251827157075159235844884000000000000000)
      constant := (35449954530395002580752131575736728180434521728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree005.table
  base := (46089803633571335519325341236781530168589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-399464447094293534286646439808000000000000000)
      constant := (1966786747723585639321007200265772072486242104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6230819941265383747/6250000000000000000)
  centralHi := (99693119060246139953/100000000000000000000)
  directionLo := (111460295553845160497/100000000000000000000)
  directionHi := (55730147776922580249/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree006.table
  base := (6509971362465951631587790514066575912641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-891215183713744421217795019363200000000000000)
      constant := (3676091678587776931082776034942540280527851760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree006.table
  base := (16203049325781298580256001337943648013331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-148718103860515771136308060375200000000000000)
      constant := (612367827000768426689584705475930122984279344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111460295553845160497/100000000000000000000)
  centralHi := (55730147776922580249/50000000000000000000)
  directionLo := (122098636282067533599/100000000000000000000)
  directionHi := (152623295352584417/125000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree007.table
  base := (22849060001995340469266858434339956948269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-8859714055020242506761074503653600000000000000)
      constant := (33062752783036192860504463891421839066399254512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree007.table
  base := (22735305476555565015269483469401699847929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-492844176068801092531201922443200000000000000)
      constant := (1837474116834550508966424072719732827225472344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/100000000000000000000)
  centralHi := (152623295352584417/125000000000000000)
  directionLo := (26376320045776455019/20000000000000000000)
  directionHi := (16485200028610284387/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree008.table
  base := (3147704967436548852260486014948305060247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-9698491456616785222561993833038400000000000000)
      constant := (34710600951861669754529446920319601094915403280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree008.table
  base := (15647840477710338045967501650759987910859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-539534040556054871653479663760800000000000000)
      constant := (1930535057444689672494512019663463044038210824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26376320045776455019/20000000000000000000)
  centralHi := (16485200028610284387/12500000000000000000)
  directionLo := (1409873610502757953/1000000000000000000)
  directionHi := (140987361050275795301/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree009.table
  base := (414145653911450793030432926169775555701/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-1170807650912591993151434795824800000000000000)
      constant := (4180179509172237427272971661376137696190066800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree009.table
  base := (10280669952229911249109497943406382652019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-195407968347769550258585801692800000000000000)
      constant := (697910017992140082627210628002306405664389528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/1000000000000000000)
  centralHi := (140987361050275795301/100000000000000000000)
  directionLo := (149539678590369209929/100000000000000000000)
  directionHi := (14953967859036920993/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree010.table
  base := (6159170055488360359734516991560306550411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-11376046259809870654163832491808000000000000000)
      constant := (41543994333006056170472120698148063096027754128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree010.table
  base := (3049962122155244166475443732602105227099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-632913769530562429898035146396000000000000000)
      constant := (2313105889105654215246747195270577244430918928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149539678590369209929/100000000000000000000)
  centralHi := (14953967859036920993/10000000000000000000)
  directionLo := (157628661638361411633/100000000000000000000)
  directionHi := (78814330819180705817/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree011.table
  base := (2814604521283453718533239331450621379373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 427680000000000000000000000000000000000000000
      center := (1818027)
      previous := (0)
      next := (1560645)
      square := (70854876317893322883456619142400000000000000)
      linear := (-1110438514673310306360431983744800000000000000)
      constant := (4210686057273830820884574995970505175153024464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree011.table
  base := (1383072616513513704957936863944816956871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (101199)
      previous := (0)
      next := (86505)
      square := (3936382017660740160192034396800000000000000)
      linear := (-61782148547074200820028444337600000000000000)
      constant := (234526407762172243619652448767015770179050992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157628661638361411633/100000000000000000000)
  centralHi := (78814330819180705817/50000000000000000000)
  directionLo := (16532233505153238537/10000000000000000000)
  directionHi := (165322335051532385371/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree012.table
  base := (24224865929244773677565393229718421823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-1450400118111439565085074572286400000000000000)
      constant := (5759704585222071721778851016454015365382127424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree012.table
  base := (57045294171647865383589544356013167569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-242097832835023329380863543010400000000000000)
      constant := (962658044488281491282063374234829586715861128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16532233505153238537/10000000000000000000)
  centralHi := (165322335051532385371/100000000000000000000)
  directionLo := (86336773688679780039/50000000000000000000)
  directionHi := (172673547377359560079/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree013.table
  base := (-1072217578651194910850000713755150188983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-13892378464599498801566590479962400000000000000)
      constant := (58032580505584691289439433675802109207786651232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree013.table
  base := (-2177330797837486628927092937054118669367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-772983362992323767264868370348800000000000000)
      constant := (3233737603572696723060831196541603554457424088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/50000000000000000000)
  centralHi := (172673547377359560079/100000000000000000000)
  directionLo := (179724326291326905781/100000000000000000000)
  directionHi := (89862163145663452891/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree014.table
  base := (-4013848429605644779885480014229360142917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-14731155866196041517367509809347200000000000000)
      constant := (64854126481298362003597685084164725979484983184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree014.table
  base := (-2020527748196451664969990026392887634781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-819673227479577546387146111666400000000000000)
      constant := (3614360858065584335073139555539190977554727568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179724326291326905781/100000000000000000000)
  centralHi := (89862163145663452891/50000000000000000000)
  directionLo := (37301749534230397923/20000000000000000000)
  directionHi := (11656796729446999351/6250000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree015.table
  base := (-5585713544467843457219234010009041155781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-1729992585310287137018714348748000000000000000)
      constant := (8029665608338965478253290236185682400705015568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree015.table
  base := (-350514580810223215921553208329128319923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-288787697322277108503141284328000000000000000)
      constant := (1342635700651491443475085573963336145229293184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37301749534230397923/20000000000000000000)
  centralHi := (11656796729446999351/6250000000000000000)
  directionLo := (193054894925903253463/100000000000000000000)
  directionHi := (24131861865737906683/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree016.table
  base := (-6914167870169912719084952702590747000799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-16408710669389126948969348468116800000000000000)
      constant := (80245703670208647709519188942281988254968112048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree016.table
  base := (-108325082366826590755994973645320629719/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-913052956454085104631701594301600000000000000)
      constant := (4472966531069839900316605727560377601386509824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193054894925903253463/100000000000000000000)
  centralHi := (24131861865737906683/12500000000000000000)
  directionLo := (39877247624098455981/20000000000000000000)
  directionHi := (99693119060246139953/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree017.table
  base := (-8039341309696613371862604940600589299821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-17247488070985669664770267797501600000000000000)
      constant := (88771387034172862467476571949098808965077810192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree017.table
  base := (-4027376828249758864839484741424339921569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-959742820941338883753979335619200000000000000)
      constant := (4948494169990407777163721490656716903619745232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39877247624098455981/20000000000000000000)
  centralHi := (99693119060246139953/50000000000000000000)
  directionLo := (3211291094005250627/1562500000000000000)
  directionHi := (205522630016336040129/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree018.table
  base := (-2247853426885068935649266985668511894257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-2009585052509134708952354125209600000000000000)
      constant := (10869982502162400640050461416485442185053592384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree018.table
  base := (-9004143748595573133089783557344078466563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-335477561809530887625419025645600000000000000)
      constant := (1817901410673544411419434017530818388399303144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3211291094005250627/1562500000000000000)
  centralHi := (205522630016336040129/100000000000000000000)
  directionLo := (4229620831508273859/2000000000000000000)
  directionHi := (211481041575413692951/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree019.table
  base := (-4896668539990153776924179245493310405389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-18925042874178755096372106456271200000000000000)
      constant := (107410272395920262784189016564951601212811111456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree019.table
  base := (-9803836256033018585099739097925965632439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1053122549915846441998534818254400000000000000)
      constant := (5987999229689225115594731558653656962230574296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4229620831508273859/2000000000000000000)
  centralHi := (211481041575413692951/100000000000000000000)
  directionLo := (217276115674990742787/100000000000000000000)
  directionHi := (54319028918747685697/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree020.table
  base := (-5231357434135087370489028212246341366979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-19763820275775297812173025785656000000000000000)
      constant := (117504395159818022996322178886770266393174926816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree020.table
  base := (-10471360223658568221326586498288297651307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1099812414403100221120812559572000000000000000)
      constant := (6550921023880069700524504484550737052585440248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217276115674990742787/100000000000000000000)
  centralHi := (54319028918747685697/25000000000000000000)
  directionLo := (44584118221538064199/20000000000000000000)
  directionHi := (55730147776922580249/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree021.table
  base := (-11013133562738381254497114509952996185971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-2289177519707982280885993901671200000000000000)
      constant := (14233979897105869152260407000734211983366923888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree021.table
  base := (-5510120280864590194707962863996582106831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-382167426296784666747696766963200000000000000)
      constant := (2380705375846230375224518476493073553370576656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44584118221538064199/20000000000000000000)
  centralHi := (55730147776922580249/25000000000000000000)
  directionLo := (57106408044977844273/25000000000000000000)
  directionHi := (228425632179911377093/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree022.table
  base := (-178986374272599442843165636665050100991/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 427680000000000000000000000000000000000000000
      center := (1818027)
      previous := (0)
      next := (1560645)
      square := (70854876317893322883456619142400000000000000)
      linear := (-1949215916269853022161351313129600000000000000)
      constant := (12655417097037257988728612854398084785972282368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree022.table
  base := (-2865240141721022053992369657515105217641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (101199)
      previous := (0)
      next := (86505)
      square := (3936382017660740160192034396800000000000000)
      linear := (-108472013034327979942306185655200000000000000)
      constant := (705573686293102399458638344668176440011539936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57106408044977844273/25000000000000000000)
  centralHi := (228425632179911377093/100000000000000000000)
  directionLo := (233801088393066012937/100000000000000000000)
  directionHi := (116900544196533006469/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree023.table
  base := (-2359378831355198873712980893941176680529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-22280152480564925959575783773810400000000000000)
      constant := (150811846293629451363772325780031281564992465040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree023.table
  base := (-11801673049563567678229773309576767198991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1239882007864861558487645783524800000000000000)
      constant := (8408291207082708452697692855608351612487171224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233801088393066012937/100000000000000000000)
  centralHi := (116900544196533006469/50000000000000000000)
  directionLo := (59763925380812070077/25000000000000000000)
  directionHi := (239055701523248280309/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree024.table
  base := (-6022412183778787438940198253593498280839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-2568769986906829852819633678132800000000000000)
      constant := (18101065173037570688016444405373921315727967584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree024.table
  base := (-12048733695018654435067635421414599269349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-428857290784038445869974508280800000000000000)
      constant := (3027630662974905411217106907646236011165431512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59763925380812070077/25000000000000000000)
  centralHi := (239055701523248280309/100000000000000000000)
  directionLo := (122098636282067533599/50000000000000000000)
  directionHi := (244197272564135067199/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree025.table
  base := (-6101956334013954832277464272064361438713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-23957707283758011391177622432580000000000000000)
      constant := (175500459402535752489558211369818605579760693152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree025.table
  base := (-6103552899577540237939275189681325051439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1333261736839369116732201266160000000000000000)
      constant := (9784983174048357525631064986566227776911180592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/50000000000000000000)
  centralHi := (244197272564135067199/100000000000000000000)
  directionLo := (249232797650615349881/100000000000000000000)
  directionHi := (124616398825307674941/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree026.table
  base := (-12278065759933512298192136123636162500689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-24796484685354554106978541761964800000000000000)
      constant := (188582626929199056440210069810408514623875861328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree026.table
  base := (-767541883459582080415552154954398527951/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1379951601326622895854479007477600000000000000)
      constant := (10514463334560560430423187283782589441175562624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249232797650615349881/100000000000000000000)
  centralHi := (124616398825307674941/50000000000000000000)
  directionLo := (254168579729561929419/100000000000000000000)
  directionHi := (12708428986478096471/5000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree027.table
  base := (-12270342495299233703354409847796538194181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-2848362454105677424753273454594400000000000000)
      constant := (22461627789612295664038338604018254355513770768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree027.table
  base := (-6136231882205105696611114172953114451137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-475547155271292224992252249598400000000000000)
      constant := (3757084364613446084532078536539614933803388912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254168579729561929419/100000000000000000000)
  centralHi := (12708428986478096471/5000000000000000000)
  directionLo := (259010321066039340117/100000000000000000000)
  directionHi := (129505160533019670059/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree028.table
  base := (-12183139435931598524088773381012677472087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-26474039488547639538580380420734400000000000000)
      constant := (216215401476761810192220510058214947908611615024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree028.table
  base := (-6092432490479779902749432076275973356453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1473331330301130454099034490112800000000000000)
      constant := (12055290292779142390131460109594102320711488784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259010321066039340117/100000000000000000000)
  centralHi := (129505160533019670059/50000000000000000000)
  directionLo := (263763200457764550191/100000000000000000000)
  directionHi := (16485200028610284387/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree029.table
  base := (-18778648628960336854240123424114663319/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-27312816890144182254381299750119200000000000000)
      constant := (230763997284235384543512594443914422117377976320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree029.table
  base := (-2403947411062026496150410247707772332427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1520021194788384233221312231430400000000000000)
      constant := (12866526232944182723881565570815598311598439640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263763200457764550191/100000000000000000000)
  centralHi := (16485200028610284387/6250000000000000000)
  directionLo := (16776996133647111001/6250000000000000000)
  directionHi := (268431938138353776017/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree030.table
  base := (-11777402535585570205458245646900586485339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-3127954921304524996686913231056000000000000000)
      constant := (27311082729801311789856982225897712543238359792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree030.table
  base := (-2944635059718702996715336896253547005501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-522237019758546004114529990916000000000000000)
      constant := (4568307583068177385350817288629356393952301152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16776996133647111001/6250000000000000000)
  centralHi := (268431938138353776017/100000000000000000000)
  directionLo := (273020850686725191591/100000000000000000000)
  directionHi := (34127606335840648949/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree031.table
  base := (-11461496927029167339098279212379413435643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-28990371693337267685983138408888800000000000000)
      constant := (261322099842724192329375086508148804708028621936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree031.table
  base := (-1146241920247236378471065443575470655203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1613400923762891791465867714065600000000000000)
      constant := (14570449924443671432558457351904164989556143920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273020850686725191591/100000000000000000000)
  centralHi := (34127606335840648949/12500000000000000000)
  directionLo := (6938347444037610791/2500000000000000000)
  directionHi := (277533897761504431641/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree032.table
  base := (-1383940563763675912035448735515440868349/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-29829149094933810401784057738273600000000000000)
      constant := (277330636781564329748295647961915454994935597184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree032.table
  base := (-346008480851212812123210338843643430671/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1660090788250145570588145455383200000000000000)
      constant := (15463084303140069479437414878274641129471447808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6938347444037610791/2500000000000000000)
  centralHi := (277533897761504431641/100000000000000000000)
  directionLo := (1409873610502757953/500000000000000000)
  directionHi := (281974722100551590601/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree033.table
  base := (-2121639246326846676915366970373357969667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47520000000000000000000000000000000000000000
      center := (202003)
      previous := (0)
      next := (173405)
      square := (7872764035321480320384068793600000000000000)
      linear := (-309777035318488415329141182501600000000000000)
      constant := (2967929504254831465174932196411954014640712080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree033.table
  base := (-2652200121511110938463261315875076018301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (33733)
      previous := (0)
      next := (28835)
      square := (1312127339220246720064011465600000000000000)
      linear := (-51720625840527253021527975657600000000000000)
      constant := (496448711926571767113037881254957759174022432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/500000000000000000)
  centralHi := (281974722100551590601/100000000000000000000)
  directionLo := (286346683935179177191/100000000000000000000)
  directionHi := (35793335491897397149/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree034.table
  base := (-2518017473972347082262119517197570025673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-31506703898126895833385896397043200000000000000)
      constant := (310804989843805529147919055330906650306248753984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree034.table
  base := (-5036279159471173814289499657583333567197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1753470517224653128832700938018400000000000000)
      constant := (17329605073385160573011115832635603987775478416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286346683935179177191/100000000000000000000)
  centralHi := (35793335491897397149/12500000000000000000)
  directionLo := (145326445371845092587/50000000000000000000)
  directionHi := (11626115629747607407/4000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree035.table
  base := (-9463583180091078675106051091688002680469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-32345481299723438549186815726428000000000000000)
      constant := (328270337644924962098224069214454437514978719888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree035.table
  base := (-9463977637355401973705238297268534904539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1800160381711906907954978679336000000000000000)
      constant := (18303465732173757853149635842398839571734968696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145326445371845092587/50000000000000000000)
  centralHi := (11626115629747607407/4000000000000000000)
  directionLo := (58979244618646518157/20000000000000000000)
  directionHi := (147448111546616295393/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree036.table
  base := (-8783079520210241524491069738200236634699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-3687139855702220140554192783979200000000000000)
      constant := (38468989195091217609510359606894397230631013872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree036.table
  base := (-8783397831089312575972075304736860968383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-615616748733053562359085473551200000000000000)
      constant := (6434793533216899409567855095884732467243447304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58979244618646518157/20000000000000000000)
  centralHi := (147448111546616295393/50000000000000000000)
  directionLo := (149539678590369209929/50000000000000000000)
  directionHi := (299079357180738419859/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree037.table
  base := (-8030828412025349983904702353855191606989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-34023036102916523980788654385197600000000000000)
      constant := (364656558392743527193925205827875007818875238928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree037.table
  base := (-2007771269675821150991990750737866656413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1893540110686414466199534161971200000000000000)
      constant := (20332342718973158313386676369539310468271959328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149539678590369209929/50000000000000000000)
  centralHi := (299079357180738419859/100000000000000000000)
  directionLo := (303204784574112241821/100000000000000000000)
  directionHi := (151602392287056120911/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree038.table
  base := (-1801760333808114697801046791718935130597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-34861813504513066696589573714582400000000000000)
      constant := (383577205065492618663904515301939741622723610176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree038.table
  base := (-7207248145159483329018799589938477761807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-1940229975173668245321811903288800000000000000)
      constant := (21387346633860086955667595412750567945217412248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303204784574112241821/100000000000000000000)
  centralHi := (151602392287056120911/50000000000000000000)
  directionLo := (38409353695914666957/12500000000000000000)
  directionHi := (307274829567317335657/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree039.table
  base := (-3155942122968741075089285291272217893951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-3966732322901067712487832560440800000000000000)
      constant := (44775862744483346418909668397885712252494786656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree039.table
  base := (-6312050768582519081460645941319515804523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-662306613220307341481363214868800000000000000)
      constant := (7489796021617286446650886376747574378310995624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38409353695914666957/12500000000000000000)
  centralHi := (307274829567317335657/100000000000000000000)
  directionLo := (15564583224633258629/5000000000000000000)
  directionHi := (311291664492665172581/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree040.table
  base := (-2672743688982264502697146091723094602459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-36539368307706152128191412373352000000000000000)
      constant := (422873176029073940108019314296222107180924736736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree040.table
  base := (-5345621373471248555920153386645428238383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2033609704148175803566367385924000000000000000)
      constant := (23578463655445773347671105362866635087561621912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15564583224633258629/5000000000000000000)
  centralHi := (311291664492665172581/100000000000000000000)
  directionLo := (157628661638361411633/50000000000000000000)
  directionHi := (315257323276722823267/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree041.table
  base := (-134623529163963815710112167054429451639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-37378145709302694843992331702736800000000000000)
      constant := (443248390970968995494091309118551763746730743296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree041.table
  base := (-2154030343960155783848852088951401240989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2080299568635429582688645127241600000000000000)
      constant := (24714570773012347472610243320084382354331022992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157628661638361411633/50000000000000000000)
  centralHi := (315257323276722823267/100000000000000000000)
  directionLo := (319173713479970378777/100000000000000000000)
  directionHi := (159586856739985189389/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree042.table
  base := (-3199361116223539584512257705053255151097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-4246324790099915284421472336902400000000000000)
      constant := (51567596866001923297396967242530356246741857616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree042.table
  base := (-799861929355371713271728793839497941127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-708996477707561120603640956186400000000000000)
      constant := (8625902450888016195239434343878681175747606304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319173713479970378777/100000000000000000000)
  centralHi := (159586856739985189389/50000000000000000000)
  directionLo := (323042627022478765827/100000000000000000000)
  directionHi := (80760656755619691457/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree043.table
  base := (-2019774868997031906410214695846395434929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-39055700512495780275594170361506400000000000000)
      constant := (485453088887232687861423910131676929960428521808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree043.table
  base := (-1009922214985984584432736089723099824031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2173679297609937140933200609876800000000000000)
      constant := (27067871774805302004832142901441444125998251568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323042627022478765827/100000000000000000000)
  centralHi := (80760656755619691457/25000000000000000000)
  directionLo := (326865749766742051019/100000000000000000000)
  directionHi := (16343287488337102551/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree044.table
  base := (-769243587077477658988185711755257924047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 427680000000000000000000000000000000000000000
      center := (1818027)
      previous := (0)
      next := (1560645)
      square := (70854876317893322883456619142400000000000000)
      linear := (-3626770719462938453763189971899200000000000000)
      constant := (46116592637508742450911646122298051129104357904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree044.table
  base := (-769299430580769510251851696318556712221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (101199)
      previous := (0)
      next := (86505)
      square := (3936382017660740160192034396800000000000000)
      linear := (-201851742008835538186861668290400000000000000)
      constant := (2571369342645053838052793893412347109251762904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326865749766742051019/100000000000000000000)
  centralHi := (16343287488337102551/5000000000000000000)
  directionLo := (330644670103064770741/100000000000000000000)
  directionHi := (165322335051532385371/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree045.table
  base := (552193964767997209395699875615479982541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-4525917257298762856355112113364000000000000000)
      constant := (58844071548144509122692456841885047369647383152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree045.table
  base := (552149156784589802335008228775823319967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-755686342194814899725918697504000000000000000)
      constant := (9843093113042301354532534481722844972763552504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330644670103064770741/100000000000000000000)
  centralHi := (165322335051532385371/50000000000000000000)
  directionLo := (334380886661535481493/100000000000000000000)
  directionHi := (167190443330767740747/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree046.table
  base := (972253682168363464090933286485017993917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-41572032717285408422996928349660800000000000000)
      constant := (552395449337281533587607711655067507490404529632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree046.table
  base := (1944471428834370984939616771356902139569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2313748891071698478300033833829600000000000000)
      constant := (30800520703346856953161294046150983994319775384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334380886661535481493/100000000000000000000)
  centralHi := (167190443330767740747/50000000000000000000)
  directionLo := (338075815256792274931/100000000000000000000)
  directionHi := (84518953814198068733/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree047.table
  base := (3407672736352295210337098818463931093169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-42410810118881951138797847679045600000000000000)
      constant := (575678923992462981920752705384946194454919169712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree047.table
  base := (851910982523947850777612264532067713201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2360438755558952257422311575147200000000000000)
      constant := (32098786248723214240337779576394690487008885344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338075815256792274931/100000000000000000000)
  centralHi := (84518953814198068733/25000000000000000000)
  directionLo := (341730795156852733097/100000000000000000000)
  directionHi := (170865397578426366549/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree048.table
  base := (2470835671667808460672119623333069429283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-4805509724497610428288751889825600000000000000)
      constant := (66605228787092818495589307235372132410414961952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree048.table
  base := (2470824131201968827280030095541406434447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-802376206682068678848196438821600000000000000)
      constant := (11141358498133845916148291792015113465713804528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341730795156852733097/100000000000000000000)
  centralHi := (170865397578426366549/50000000000000000000)
  directionLo := (86336773688679780039/25000000000000000000)
  directionHi := (345347094754719120157/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree049.table
  base := (3273244239892014703483732646191851799061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-44088364922075036570399686337815200000000000000)
      constant := (623699847693224370565900956601126603590329298656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree049.table
  base := (3273234997138787504542877046826770626401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2453818484533459815666867057782400000000000000)
      constant := (34776388063200633926574003780445778954183233072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/25000000000000000000)
  centralHi := (345347094754719120157/100000000000000000000)
  directionLo := (174462958355430744917/50000000000000000000)
  directionHi := (69785183342172297967/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree050.table
  base := (8222112604369593386346380104724188574299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-44927142323671579286200605667200000000000000000)
      constant := (648437284391035347858742067855569785066401815952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree050.table
  base := (822209780550190645018398744103481197691/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2500508349020713594789144799100000000000000000)
      constant := (36155723659255368839901828181258885845828519760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174462958355430744917/50000000000000000000)
  centralHi := (69785183342172297967/20000000000000000000)
  directionLo := (1409873610502757953/400000000000000000)
  directionHi := (352468402625689488251/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree051.table
  base := (9968534658922893225123343980787110349463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-5085102191696458000222391666287200000000000000)
      constant := (74851040546207845899163868444303178832187129936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree051.table
  base := (2492130704047761534233482414261921099779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-849066071169322457970474180139200000000000000)
      constant := (12520694016827014992030013916848549426485098592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/400000000000000000)
  centralHi := (352468402625689488251/100000000000000000000)
  directionLo := (355975637293474419009/100000000000000000000)
  directionHi := (35597563729347441901/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree052.table
  base := (1178574753399743574143459441415634946547/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-46604697126864664717802444325969600000000000000)
      constant := (699366085923105282442677757686984626293331430560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree052.table
  base := (5892869030272024219853211927679109244707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2593888077995221153033700281735200000000000000)
      constant := (38995463054819488820162656843924842398439324304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355975637293474419009/100000000000000000000)
  centralHi := (35597563729347441901/10000000000000000000)
  directionLo := (179724326291326905781/50000000000000000000)
  directionHi := (359448652582653811563/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree053.table
  base := (427304551545753943747635137965142886421/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-47443474528461207433603363655354400000000000000)
      constant := (725557444787578783549292224233531092300191571456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree053.table
  base := (2734747614817857731245853191860248668211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2640577942482474932155978023052800000000000000)
      constant := (40455866529451269988901087135648747295961813480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179724326291326905781/50000000000000000000)
  centralHi := (359448652582653811563/100000000000000000000)
  directionLo := (362888430981859025821/100000000000000000000)
  directionHi := (181444215490929512911/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree054.table
  base := (3126504925075317388958192217568174819073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-5364694658895305572156031442748800000000000000)
      constant := (83581493272083789215211297474777718170712919280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree054.table
  base := (3908129642485515811339692489556072565527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-895755935656576237092751921456800000000000000)
      constant := (13981097454111456623518000416047650016763484896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362888430981859025821/100000000000000000000)
  centralHi := (181444215490929512911/50000000000000000000)
  directionLo := (366295908846202600797/100000000000000000000)
  directionHi := (183147954423101300399/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree055.table
  base := (8831040511838718895391486553018138396933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 427680000000000000000000000000000000000000000
      center := (1818027)
      previous := (0)
      next := (1560645)
      square := (70854876317893322883456619142400000000000000)
      linear := (-4465548121059481169564109301284000000000000000)
      constant := (70854006208109456564737718581424584485920061088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree055.table
  base := (4415519046219692315267081597513169728809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (101199)
      previous := (0)
      next := (86505)
      square := (3936382017660740160192034396800000000000000)
      linear := (-248541606496089317309139409608000000000000000)
      constant := (3950703678687961488956731610591515165102600736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366295908846202600797/100000000000000000000)
  centralHi := (183147954423101300399/50000000000000000000)
  directionLo := (7393439587484452227/2000000000000000000)
  directionHi := (369671979374222611351/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree056.table
  base := (9881206072748913051331157745189257126409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-49959806733250835581006121643508800000000000000)
      constant := (807039330039251087390389437817219991273209722464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree056.table
  base := (19762408280171061200258341440229710824233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2780647535944236269522811247005600000000000000)
      constant := (44999210770185085474742215556802643722102153688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7393439587484452227/2000000000000000000)
  centralHi := (369671979374222611351/100000000000000000000)
  directionLo := (37301749534230397923/10000000000000000000)
  directionHi := (373017495342303979231/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree057.table
  base := (5483378968021110892822929569319428592579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-5644287126094153144089671219210400000000000000)
      constant := (92796580411348004676034251906424135685565157952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree057.table
  base := (10966756392685265580494092466909681534579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-942445800143830016215029662774400000000000000)
      constant := (15522567740691219190094461486259584291058504496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37301749534230397923/10000000000000000000)
  centralHi := (373017495342303979231/100000000000000000000)
  directionLo := (94083317905074128599/25000000000000000000)
  directionHi := (376333271620296514397/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree058.table
  base := (12087695269981891959452783987509762871657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-51637361536443921012607960302278400000000000000)
      constant := (863783748495269102212509115081512085846890584672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree058.table
  base := (6043847018945324963220570019442319857083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2874027264918743827767366729640800000000000000)
      constant := (48163217778770241164014298347371777887138885152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94083317905074128599/25000000000000000000)
  centralHi := (376333271620296514397/100000000000000000000)
  directionLo := (23726255468084723091/6250000000000000000)
  directionHi := (379620087489355569457/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree059.table
  base := (13244017421487273378765189205092521312639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-52476138938040463728408879631663200000000000000)
      constant := (892882903804181296330070630964992007932976784544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree059.table
  base := (13244016438177741324439005225740890154169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-2920717129405997606889644470958400000000000000)
      constant := (49785754406950184743322048679812977810138721968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23726255468084723091/6250000000000000000)
  centralHi := (379620087489355569457/100000000000000000000)
  directionLo := (382878688780684266477/100000000000000000000)
  directionHi := (191439344390342133239/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree060.table
  base := (2887144775538520633705152581334735624301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-5923879593293000716023310995672000000000000000)
      constant := (102496298794035031067878098920575293005534618720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree060.table
  base := (5774289237262653599281488507245082402987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-989135664631083795337307404092000000000000000)
      constant := (17145104360152369051156239981885595789474113720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382878688780684266477/100000000000000000000)
  centralHi := (191439344390342133239/50000000000000000000)
  directionLo := (386109789851806506927/100000000000000000000)
  directionHi := (24131861865737906683/6250000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree061.table
  base := (31325628471558480964920791281692221500167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-54153693741233549160010718290432800000000000000)
      constant := (952535104142660604157309968555677817220310564816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree061.table
  base := (31325627220018225866510393770844156162907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3014096858380505165134199953593600000000000000)
      constant := (53111893778757614659217408813484832865473737352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386109789851806506927/100000000000000000000)
  centralHi := (24131861865737906683/6250000000000000000)
  directionLo := (389314075415205462223/100000000000000000000)
  directionHi := (24332129713450341389/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree062.table
  base := (8462644089650310833601472793021898734417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-54992471142830091875811637619817600000000000000)
      constant := (983088148495473964014094276401148364863236035264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree062.table
  base := (4231321920075290414680759801093633094633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3060786722867758944256477694911200000000000000)
      constant := (54815496485729244351602778107024265556490624704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389314075415205462223/100000000000000000000)
  centralHi := (24332129713450341389/6250000000000000000)
  directionLo := (392492202232587531879/100000000000000000000)
  directionHi := (9812305055814688297/2500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree063.table
  base := (3644629091920497009581873614219509489837/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-6203472060491848287956950772133600000000000000)
      constant := (112680646885644173220937972396296097000527596640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree063.table
  base := (36446290123591117985244798993590180684843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1035825529118337574459585145409600000000000000)
      constant := (18848707062903257401666705271185307654126352216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392492202232587531879/100000000000000000000)
  centralHi := (9812305055814688297/2500000000000000000)
  directionLo := (395644800686646825287/100000000000000000000)
  directionHi := (49455600085830853161/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree064.table
  base := (19556385881241697200435720840980751348359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-56670025946023177307413476278587200000000000000)
      constant := (1045648124384739726614109055360241825020665589664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree064.table
  base := (39112771128372557064764649009176115937087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3154166451842266502501033177546400000000000000)
      constant := (58303767877751521607294233064372626966131705832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395644800686646825287/100000000000000000000)
  centralHi := (49455600085830853161/12500000000000000000)
  directionLo := (398772476240984559811/100000000000000000000)
  directionHi := (99693119060246139953/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree065.table
  base := (41850018581086110862246137852787285420923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-57508803347619720023214395607972000000000000000)
      constant := (1077655055592708083377443270505004947851702383504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree065.table
  base := (20925009037908944888479522372478876542677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3200856316329520281623310918864000000000000000)
      constant := (60088436545036463528123968347615465834638812144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398772476240984559811/100000000000000000000)
  centralHi := (99693119060246139953/25000000000000000000)
  directionLo := (40187581079775963333/10000000000000000000)
  directionHi := (401875810797759633331/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree066.table
  base := (44658031133237357489950561173978683894449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47520000000000000000000000000000000000000000
      center := (202003)
      previous := (0)
      next := (173405)
      square := (7872764035321480320384068793600000000000000)
      linear := (-589369502517335987262780958963200000000000000)
      constant := (11213602176575350561634106228595846705866421648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree066.table
  base := (44658030730727983223864535414161902530349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (33733)
      previous := (0)
      next := (28835)
      square := (1312127339220246720064011465600000000000000)
      linear := (-98410490327781032143805716975200000000000000)
      constant := (1875761429830831316062671179197616226804036408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40187581079775963333/10000000000000000000)
  centralHi := (401875810797759633331/100000000000000000000)
  directionLo := (404955363961692451301/100000000000000000000)
  directionHi := (202477681980846225651/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree067.table
  base := (9507361845727986841237864099298718230537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-59186358150812805454816234266741600000000000000)
      constant := (1143122803959969656104910107562908891970598352880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree067.table
  base := (47536808908064445225316970708213867335613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3294236045304027839867866401499200000000000000)
      constant := (63738839791058267895106004529625327636683581368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404955363961692451301/100000000000000000000)
  centralHi := (202477681980846225651/50000000000000000000)
  directionLo := (204005837109098979083/50000000000000000000)
  directionHi := (408011674218197958167/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree068.table
  base := (12621588179353093901031617553925370907229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-60025135552409348170617153596126400000000000000)
      constant := (1176583620959226499249128886362957931570256274368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree068.table
  base := (25243176231074684356806624698596176311411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3340925909791281618990144142816800000000000000)
      constant := (65604574361151529144116046942182219328150075792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204005837109098979083/50000000000000000000)
  centralHi := (408011674218197958167/100000000000000000000)
  directionLo := (3211291094005250627/781250000000000000)
  directionHi := (411045260032672080257/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree069.table
  base := (26753330740703272816751588139108834493797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-6762656994889543431824230325056800000000000000)
      constant := (134503229602571964525095631674265468993319513568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree069.table
  base := (53506661278193527257549845354697010935517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1129205258092845132704140628044800000000000000)
      constant := (22499110297232361985030780264117470359270224104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3211291094005250627/781250000000000000)
  centralHi := (411045260032672080257/100000000000000000000)
  directionLo := (82811324175457334731/20000000000000000000)
  directionHi := (51757077609660834207/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree070.table
  base := (56597735427393333764533621122832697839793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-61702690355602433602218992254896000000000000000)
      constant := (1244959140307873751944588825379166897033334937264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree070.table
  base := (28298867632825453649480118502602643315451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3434305638765789177234699625452000000000000000)
      constant := (69417109380328427717678645872238045371385254672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82811324175457334731/20000000000000000000)
  centralHi := (51757077609660834207/12500000000000000000)
  directionLo := (83409247638210288211/20000000000000000000)
  directionHi := (13032694943470357533/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree071.table
  base := (29879787240857200376311655158241482717899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-62541467757198976318019911584280800000000000000)
      constant := (1279873842578752294524372316578245053123340297504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree071.table
  base := (29879787176502872941451812630316587176891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3480995503253042956356977366769600000000000000)
      constant := (71363909825176418451284629456872958644910446352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83409247638210288211/20000000000000000000)
  centralHi := (13032694943470357533/3125000000000000000)
  directionLo := (105003644069592090931/25000000000000000000)
  directionHi := (16800583051134734549/4000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree072.table
  base := (62992178586084456885881536200052811925709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-7042249462088391003757870101518400000000000000)
      constant := (146141463689818123387870177669867560584980660848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree072.table
  base := (31496089241841586899027750500960832974137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1175895122580098911826418369362400000000000000)
      constant := (24445910741587472458067704725307141553741363088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105003644069592090931/25000000000000000000)
  centralHi := (16800583051134734549/4000000000000000000)
  directionLo := (422962083150827385901/100000000000000000000)
  directionHi := (211481041575413692951/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree073.table
  base := (66295547694296464944369774557593238306597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-64219022560392061749621750243050400000000000000)
      constant := (1351157132174968191597921033890511098774861945456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree073.table
  base := (66295547612841179177994866586155735332107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3574375232227550514601532849404800000000000000)
      constant := (75338576577914433664293320834988216298639948552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422962083150827385901/100000000000000000000)
  centralHi := (211481041575413692951/50000000000000000000)
  directionLo := (425889191316564786451/100000000000000000000)
  directionHi := (106472297829141196613/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree074.table
  base := (69669681769635452914638543288215939778029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-65057799961988604465422669572435200000000000000)
      constant := (1387525719461295052691857339207955512436694186992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree074.table
  base := (69669681704853855739472702960533158580739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3621065096714804293723810590722400000000000000)
      constant := (77366442883701348634936253072109294632666194504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425889191316564786451/100000000000000000000)
  centralHi := (106472297829141196613/25000000000000000000)
  directionLo := (53599539815140266299/12500000000000000000)
  directionHi := (428796318521122130393/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree075.table
  base := (36557290391424221902235604407942782674271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-7321841929287238575691509877980000000000000000)
      constant := (158264326117064632139178464905395845271898987424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree075.table
  base := (73114580731336881094216237036868373554633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1222584987067352690948696110680000000000000000)
      constant := (26473777047127103212064004563283947270407962696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53599539815140266299/12500000000000000000)
  centralHi := (428796318521122130393/100000000000000000000)
  directionLo := (86336773688679780039/20000000000000000000)
  directionHi := (107920967110849725049/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree076.table
  base := (7663024471055083056917899530147042480921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-66735354765181689897024508231204800000000000000)
      constant := (1461716778940826859665207823496364558410643226080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree076.table
  base := (3065209786783932558798416864776589534357/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3714444825689311851968366073357600000000000000)
      constant := (81503241350361240090968683414707823601748863800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/20000000000000000000)
  centralHi := (107920967110849725049/25000000000000000000)
  directionLo := (17382089253999259423/4000000000000000000)
  directionHi := (54319028918747685697/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree077.table
  base := (50135420958734550422424274912651548429/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 427680000000000000000000000000000000000000000
      center := (1818027)
      previous := (0)
      next := (1560645)
      square := (70854876317893322883456619142400000000000000)
      linear := (-6143102924252566601165947960053600000000000000)
      constant := (136321750101291046352202953280306075277138355200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree077.table
  base := (80216673501423010667590522948756162610021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (101199)
      previous := (0)
      next := (86505)
      square := (3936382017660740160192034396800000000000000)
      linear := (-341921335470596875553694892243200000000000000)
      constant := (7601106682742279000322381778649194642361409896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17382089253999259423/4000000000000000000)
  centralHi := (54319028918747685697/12500000000000000000)
  directionLo := (437401784710851328397/100000000000000000000)
  directionHi := (218700892355425664199/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree078.table
  base := (83873867237989467660862081495058821073649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-7601434396486086147625149654441600000000000000)
      constant := (170871816840731851906609039973420614695161780528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree078.table
  base := (83873867212118735583497632761200163906669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1269274851554606470070973851997600000000000000)
      constant := (28582709206802933368062879904923975827954900328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437401784710851328397/100000000000000000000)
  centralHi := (218700892355425664199/50000000000000000000)
  directionLo := (27514555861201394709/6250000000000000000)
  directionHi := (88046578755844463069/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree079.table
  base := (43800912905162394690842371324902302537229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-69251686969971318044427266219359200000000000000)
      constant := (1576638080292210592180245960175301551848068617184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree079.table
  base := (8760182578976755066701228728677888315661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3854514419151073189335199297310400000000000000)
      constant := (87911103680780946164003706758508302890181158960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27514555861201394709/6250000000000000000)
  centralHi := (88046578755844463069/20000000000000000000)
  directionLo := (44304591213802903229/10000000000000000000)
  directionHi := (443045912138029032291/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree080.table
  base := (91400549240970680912283371977619525635037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-70090464371567860760228185548744000000000000000)
      constant := (1615914437286363834688189588767687150595951886576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree080.table
  base := (11425068653079779240566485781175036414571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3901204283638326968457477038628000000000000000)
      constant := (90101101691027171964966603135534326013849821248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44304591213802903229/10000000000000000000)
  centralHi := (443045912138029032291/100000000000000000000)
  directionLo := (44584118221538064199/10000000000000000000)
  directionHi := (445841182215380641991/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree081.table
  base := (95270037521698899014264871649718696567913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-7881026863684933719558789430903200000000000000)
      constant := (183963935838352826012032965494509570706997948336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree081.table
  base := (47635018754362509427246363653424047519831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1315964716041860249193251593315200000000000000)
      constant := (30772707216979412931264153307144610603985535344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44584118221538064199/10000000000000000000)
  centralHi := (445841182215380641991/100000000000000000000)
  directionLo := (448619035771107629787/100000000000000000000)
  directionHi := (112154758942776907447/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree082.table
  base := (19842058129137964302825281841706117877189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-71768019174760946191830024207513600000000000000)
      constant := (1695921036065437112828287201699998898715439053360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree082.table
  base := (49605145317692715384939708304133574571229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-3994584012612834526702032521263200000000000000)
      constant := (94562163560340538932061442782520870209987282288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448619035771107629787/100000000000000000000)
  centralHi := (112154758942776907447/25000000000000000000)
  directionLo := (28211237147272403577/6250000000000000000)
  directionHi := (451379794356358457233/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree083.table
  base := (25805327151809705319145137498699210570153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-72606796576357488907630943536898400000000000000)
      constant := (1736651277844465140421619422455346659857229354176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree083.table
  base := (1290266357488198326175943027669933383989/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4041273877100088305824310262580800000000000000)
      constant := (96833227419088662036695102562729960313914920320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28211237147272403577/6250000000000000000)
  centralHi := (451379794356358457233/100000000000000000000)
  directionLo := (113530942437012120381/25000000000000000000)
  directionHi := (18164950789921939261/4000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree084.table
  base := (107303091401525495934488718016468844985447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-8160619330883781291492429207364800000000000000)
      constant := (197540683097776863137275304768702459465079285584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree084.table
  base := (107303091395028164958480434214499941963939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1362654580529114028315529334632800000000000000)
      constant := (33043771075686518547122566664712323494389836568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113530942437012120381/25000000000000000000)
  centralHi := (18164950789921939261/4000000000000000000)
  directionLo := (57106408044977844273/12500000000000000000)
  directionHi := (91370252871964550837/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree085.table
  base := (111455639024432239821683103999297492142601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-74284351379550574339232782195668000000000000000)
      constant := (1819565646170079876919424849551473381583502355248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree085.table
  base := (111455639019274038782181660214721115477797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4134653606074595864068865745216000000000000000)
      constant := (101456420984147936395728499902833201074127702392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57106408044977844273/12500000000000000000)
  centralHi := (91370252871964550837/20000000000000000000)
  directionLo := (229781285815533049531/50000000000000000000)
  directionHi := (459562571631066099063/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree086.table
  base := (57839475736200776187015195494472758156041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-75123128781147117055033701525052800000000000000)
      constant := (1861749772713055847448065351660266340257986352736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree086.table
  base := (925431611746456376777277219888723771437/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4181343470561849643191143486533600000000000000)
      constant := (103808550690262682691705345480275260561284679000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229781285815533049531/50000000000000000000)
  centralHi := (459562571631066099063/100000000000000000000)
  directionLo := (28891123524711058623/6250000000000000000)
  directionHi := (462257976395376937969/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree087.table
  base := (119973028742323759258202755984708184421041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-8440211798082628863426068983826400000000000000)
      constant := (211602058611939637750070426841073941216056655152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree087.table
  base := (119973028739074039642064528233723570956391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1409344445016367807437807075950400000000000000)
      constant := (35395900781774665798022532063245349750172078392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28891123524711058623/6250000000000000000)
  centralHi := (462257976395376937969/100000000000000000000)
  directionLo := (92987551045962913973/20000000000000000000)
  directionHi := (232468877614907284933/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree088.table
  base := (3885558463482769167342023853373906561419/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 427680000000000000000000000000000000000000000
      center := (1818027)
      previous := (0)
      next := (1560645)
      square := (70854876317893322883456619142400000000000000)
      linear := (-6981880325849109316966867289438400000000000000)
      constant := (177051991868362609597306439825048647546200569344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree088.table
  base := (62168935414434861204980433213922249094231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23760000000000000000000000000000000000000000
      center := (101199)
      previous := (0)
      next := (86505)
      square := (3936382017660740160192034396800000000000000)
      linear := (-388611199957850654675972633560800000000000000)
      constant := (9872170540841924994422726169743758527695785712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92987551045962913973/20000000000000000000)
  centralHi := (232468877614907284933/50000000000000000000)
  directionLo := (233801088393066012937/50000000000000000000)
  directionHi := (3740817414289056207/800000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree089.table
  base := (128773477737315648170396008996774628358229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-77639460985936745202436459513207200000000000000)
      constant := (1991209921845494223366172701854787905361872116592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree089.table
  base := (64386738867634686609644982557952392917001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4321413064023610980557976710486400000000000000)
      constant := (111027071502010842786515302278379337482557476272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233801088393066012937/50000000000000000000)
  centralHi := (3740817414289056207/800000000000000000)
  directionLo := (94050300421023466609/20000000000000000000)
  directionHi := (235125751052558666523/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree090.table
  base := (133279849457699259229692532472923607333563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-8719804265281476435359708760288000000000000000)
      constant := (226148062376325140218227625820147162802540005136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree090.table
  base := (133279849456075804519930909274718808577863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1456034309503621586560084817268000000000000000)
      constant := (37829096334505191747951193062761350260330342456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94050300421023466609/20000000000000000000)
  centralHi := (235125751052558666523/50000000000000000000)
  directionLo := (472885984915084234899/100000000000000000000)
  directionHi := (4728859849150842349/1000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree091.table
  base := (34464246497641338655327355636317433531247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-79317015789129830634038298171976800000000000000)
      constant := (2079939829175327886892405558235094330879632354624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree091.table
  base := (68928492994638756054359987463015487656307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4414792792998118538802532193121600000000000000)
      constant := (115974528453722799636810931506999795570770479504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472885984915084234899/100000000000000000000)
  centralHi := (4728859849150842349/1000000000000000000)
  directionLo := (237752935957739214631/50000000000000000000)
  directionHi := (475505871915478429263/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree092.table
  base := (142504887334037095196353861091377802900357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-80155793190726373349839217501361600000000000000)
      constant := (2125031725209816142927325150916034104618867149936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree092.table
  base := (1140039098664124864518685347821473888223/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4461482657485372317924809934439200000000000000)
      constant := (118488789852583932070688768678001955192824541000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237752935957739214631/50000000000000000000)
  centralHi := (475505871915478429263/100000000000000000000)
  directionLo := (478111403046496560617/100000000000000000000)
  directionHi := (239055701523248280309/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree093.table
  base := (73611776743183889038149084257563242122569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-8999396732480324007293348536749600000000000000)
      constant := (241178694387729921910334424512611966584461853536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree093.table
  base := (1840294418569470670344443947673105798183/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1502724173990875365682362558585600000000000000)
      constant := (40343357733351231175345616039266397817101623680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478111403046496560617/100000000000000000000)
  centralHi := (239055701523248280309/50000000000000000000)
  directionLo := (240351405872775988489/50000000000000000000)
  directionHi := (480702811745551976979/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree094.table
  base := (152012984445919335548301342754466543321667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-81833347993919458781441056160131200000000000000)
      constant := (2216669402013816724010088943589428176372591596816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree094.table
  base := (38003246111319228399217070526043455449591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4554862386459879876169365417074400000000000000)
      constant := (123598378496089567651667676192865487006522041504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240351405872775988489/50000000000000000000)
  centralHi := (480702811745551976979/100000000000000000000)
  directionLo := (483280325191363120079/100000000000000000000)
  directionHi := (6041004064892039001/1250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree095.table
  base := (39218295052786312455071938800153028971739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-82672125395516001497241975489516000000000000000)
      constant := (2263215182781830867176316124516049443694786676288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree095.table
  base := (78436590105317936098511891163233122732273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4601552250947133655291643158392000000000000000)
      constant := (126193705740651369935266246067460771791461374256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483280325191363120079/100000000000000000000)
  centralHi := (6041004064892039001/1250000000000000000)
  directionLo := (485844164536386903609/100000000000000000000)
  directionHi := (48584416453638690361/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree096.table
  base := (32360828156115388369000593045882082540307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2222033)
      previous := (0)
      next := (1907455)
      square := (86600404388536283524224756729600000000000000)
      linear := (-9278989199679171579226988313211200000000000000)
      constant := (256693954643657870735118734034513341092734637520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree096.table
  base := (161804140780173100072352787783882328298023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (371063)
      previous := (0)
      next := (317185)
      square := (14433400731422713920704126121600000000000000)
      linear := (-1549414038478129144804640299903200000000000000)
      constant := (42938684977900301486397595593454782844132376376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485844164536386903609/100000000000000000000)
  centralHi := (48584416453638690361/10000000000000000000)
  directionLo := (122098636282067533599/25000000000000000000)
  directionHi := (488394545128270134397/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree097.table
  base := (166805866152812894709542044496586516787279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-84349680198709086928843814148285600000000000000)
      constant := (2357760629046427291500704091243432608649541830992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree097.table
  base := (166805866152492757982681691422232155815319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4694931979921641213536198641027200000000000000)
      constant := (131465426075201689569066120937607909624389177384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell184.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/25000000000000000000)
  centralHi := (488394545128270134397/100000000000000000000)
  directionLo := (490931676720946573631/100000000000000000000)
  directionHi := (7670807448764790213/1562500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree098.table
  base := (34375671265301986171539373535215350972271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704480000000000000000000000000000000000000000
      center := (19998297)
      previous := (0)
      next := (17167095)
      square := (779403639496826551718022810566400000000000000)
      linear := (-85188457600305629644644733477670400000000000000)
      constant := (2405760294541718336635259579171091057171014737040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree098.table
  base := (85939178163128088220021674660951081809027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 261360000000000000000000000000000000000000000
      center := (1113189)
      previous := (0)
      next := (951555)
      square := (43300202194268141762112378364800000000000000)
      linear := (-4741621844408894992658476382344800000000000000)
      constant := (134141819165118737799148739265708434948321459344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell184.Kernel098
