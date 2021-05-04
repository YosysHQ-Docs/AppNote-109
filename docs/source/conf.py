# https://stackoverflow.com/questions/40641252/how-can-i-avoid-the-horizontal-scrollbar-in-a-rest-table
def setup(app):
        app.add_stylesheet('custom.css')

# These folders are copied to the documentation's HTML output
html_static_path = ['_static']

# These paths are either relative to html_static_path
# or fully qualified paths (eg. https://...)
html_css_files = [
    'css/custom.css',
]

# code blocks style 
pygments_style = 'colorful'
highlight_language = 'systemverilog'

