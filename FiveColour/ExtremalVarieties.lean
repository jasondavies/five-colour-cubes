module
public import FiveColour.ExtremalTriples
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

def extremalB : Fin 5 → Fin 75 := ![16,16,17,17,22]
def extremalC : Fin 5 → Fin 75 := ![49,59,49,50,50]
def extremalBGroup : Fin 3 → Fin 75 := ![16,17,22]
def extremalCGroup : Fin 3 → Fin 75 := ![49,50,59]
end FiveColour.Physical
