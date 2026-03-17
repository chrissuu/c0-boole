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
  | .ok tokens => IO.println tokens
  | .error err => IO.eprintln err
