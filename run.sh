if [ "$#" -lt 1 ]; then
  echo "Usage: $0 file"
  exit 1
fi

SRC=$1

start_iso=$(date -Iseconds)

g++ -std=c++23 -O3 "$SRC" -o run_binary

echo "Execution start: $start_iso";

./run_binary

end_iso=$(date -Iseconds)

echo "Time: $end_iso";
