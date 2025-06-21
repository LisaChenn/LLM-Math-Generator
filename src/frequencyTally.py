#-------------------------------------------------------------------
#   IMPORTS
#-------------------------------------------------------------------
from openai import OpenAI
from dotenv import load_dotenv
import random
from datasets import load_dataset
import numpy as np


#-------------------------------------------------------------------
#   VARS
#-------------------------------------------------------------------
arithmetic = 0

conversion = 0 

ratios = 0

fractions = 0

percentages = 0 



# Load the GSM8K training split
dataset = load_dataset("openai/gsm8k", "main", split="train")

# Select the first 1000 problems
subset = dataset.select(range(7473))

load_dotenv()
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))



#-------------------------------------------------------------------
#  FUNCTIONS
#-------------------------------------------------------------------
def check_Linear_System(client, problem):
    print("Checking... \n")

    system_prompt = (
        "You are a professional math problem category sorter."
        f"{problem}\n\n"
        ""    
        "Only return True if the problem can be made into a system of equation. Return False if the problem cannot be made into a system of equation"
        )

    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": "Tell me in only True and False statements"}
        ]
    )
    print(response.choices[0].message.content.strip() + "\n")
    return response.choices[0].message.content.strip()

#-------------------------------------------------------------------
#   RUN CODE
#-------------------------------------------------------------------
for i in range(7473):
    print("Number: ", i)
    print("Counter: ", counter)  
    if(check_Linear_System(client, subset[i]['question']) == 'True'):
        counter += 1


