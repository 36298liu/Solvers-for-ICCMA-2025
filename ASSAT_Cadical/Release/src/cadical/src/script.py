import os
import sys

def scan_cpp_files(folder_path):
    if not os.path.isdir(folder_path):
        print("Invalid directory path.")
        return
    
    cpp_files = [f[:-4] for f in os.listdir(folder_path) if f.endswith(".cpp")]
    
    if not cpp_files:
        print("No .cpp files found.")
        return
    
    first_part = "\n".join([f"../src/cadical/src/{file}.cpp \\" for file in cpp_files])
    second_part = "\n".join([f"./src/cadical/src/{file}.d \\" for file in cpp_files])
    third_part = "\n".join([f"./src/cadical/src/{file}.o \\" for file in cpp_files])
    
    print(first_part)
    print(second_part)
    print(third_part)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python script.py <folder_path>")
    else:
        scan_cpp_files(sys.argv[1])