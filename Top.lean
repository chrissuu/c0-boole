import C0Boole

def simpleProgram :=
"
//test return 26
int main() {
  int x = 10;
  x += 5;
  x *= 2;
  x -= 4;
  return x;
}
"
def main : IO Unit :=
  let lexedProgram := C0Boole.Lexer.munch "" simpleProgram
  match lexedProgram with
  | .error err => IO.eprintln err
  | .ok tokens => do
    let _ ← IO.println tokens
    let parsedProgram := C0Boole.Parse.parseProgramFromTokens tokens
    match parsedProgram with
    | .error err => IO.eprintln err
    | .ok program => IO.println program
