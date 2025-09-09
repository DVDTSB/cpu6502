
import base64

name = input()

data = input()

data_bytes = base64.b64decode(data)

with open(f"{name}.bin", "wb") as f:
    f.write(data_bytes)

    
